"""Unit tests for AKCM editorial rules, axiom parser, and site helpers."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

from editorial import (
    _validate_press_release,
    bump_family_versions_for_issue,
    is_blocked_family,
    load_blocklist,
    register_families,
    render_editorial,
    run_namer,
)
from msc2020 import section_prefix, section_title
from pipeline import publish_next_issue, run_launch
from verify import ALLOWED_AXIOMS, extract_theorem_name, parse_axioms


def test_blocklist() -> None:
    bl = load_blocklist()
    for real in ("GPT", "Claude", "Gemini", "Llama", "DeepSeek", "Euler", "Gauss", "Ramanujan", "Thurston", "Borges"):
        assert is_blocked_family(real, bl), f"Expected '{real}' to be blocked"
    for invented in ("Kagu", "Cassowary", "Noumenon", "Aletheia", "Lapita", "Kakapo"):
        assert not is_blocked_family(invented, bl), f"Expected '{invented}' to be allowed"


def test_press_release_rules() -> None:
    good = (
        "Today we announce the first kernel-checked benchmark milestone in our series, "
        "setting a new state of the art across formal verification evaluations without explaining math."
    )
    assert _validate_press_release(good)
    assert not _validate_press_release("A new state of the art theorem without the f-word and too short.")
    assert not _validate_press_release("The first theorem in a long paragraph that forgets the magic phrase completely.")


def test_press_release_uses_current_title() -> None:
    editorial = {
        "title": "The First Title",
        "proved_by": "Petrel-1.0-Turbo",
        "press_release_body": "This marks the first milestone and advances the state of the art.",
    }
    renamed = editorial | {"title": "The Revised Title"}
    display = render_editorial(renamed)
    assert display["eponym"] == "The Revised Title | proved by Petrel-1.0-Turbo"
    assert "announce The Revised Title, proved by Petrel-1.0-Turbo." in display["press_release"]
    assert "The First Title" not in display["press_release"]

    legacy = {
        "title": renamed["title"],
        "eponym": display["eponym"],
        "press_release": "Today we are proud to announce The First Title, proved by Petrel-1.0-Turbo, marking a milestone.",
    }
    assert render_editorial(legacy)["press_release"] == (
        "Today we are proud to announce The Revised Title, proved by Petrel-1.0-Turbo, marking a milestone."
    )


def test_live_namer_leaves_title_out_of_press_body() -> None:
    body = (
        "This marks the first milestone of its tier in our evaluations. "
        "We advance the state of the art across formal verification benchmarks."
    )
    response = {
        "title": "The Initial Theorem",
        "models": [{"family": "Petrel", "version": "1.0", "tier": "Turbo"}],
        "press_release_body": body,
    }
    with patch("editorial.chat_completion"), patch(
        "editorial.extract_json",
        side_effect=[response | {"press_release_body": f"The Initial Theorem. {body}"}, response],
    ) as extract:
        named = run_namer(
            {"statement_lean": "theorem demo : True"},
            kind="Theorem",
            joint_eponym=False,
            families_state={},
            blocklist=set(),
            deprecate_after=50,
            model="example",
            endpoint="unused",
        )
    assert extract.call_count == 2
    assert named["press_release_body"] == body
    assert "announce The Initial Theorem" in render_editorial(named)["press_release"]


def test_launch_replaces_issue_only_after_full_verification() -> None:
    first_id = "AKCM-2026-0001"
    prior_issue = {
        "number": 1,
        "volume": 1,
        "date": "2026-11-24",
        "published_at": "2026-11-24T00:35:12Z",
        "result_ids": [first_id],
    }
    candidate = {
        "statement_hash": "first",
        "statement_lean": "theorem candidate : True",
        "lean_file": "theorem candidate : True := trivial\n",
        "proof_shape": {"depth": 8, "joins": 1, "specialist_symbols": ["Example"]},
        "novelty": {"level_2_not_routine": True},
    }
    with TemporaryDirectory() as directory:
        root = Path(directory)
        (root / "state").mkdir()
        issue_path = root / "state" / "issues.json"
        issue_path.write_text(json.dumps({"issues": [prior_issue]}), encoding="utf-8")
        families_path = root / "state" / "families.json"
        families_path.write_text('{"families": {}}', encoding="utf-8")
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.36.0", encoding="utf-8")
        initial = root / "results" / first_id
        initial.mkdir(parents=True)
        initial_meta = initial / "meta.json"
        initial_meta.write_text(
            json.dumps({"id": first_id, "issue": 1, "verified": True, "statement_hash": "old"}),
            encoding="utf-8",
        )
        proof = initial / "Result.lean"
        proof.write_text("theorem original : True := trivial\n", encoding="utf-8")

        cfg = {"journal": {"id_prefix": "AKCM"}}
        editorial = {"title": "Example Theorem", "mean_importance": 1, "msc_code": "00A00"}
        profiles = (("Module.One", "Focus.One"), ("Module.Two", "Focus.Two"))
        with (
            patch("pipeline.ROOT", root),
            patch("editorial.ROOT", root),
            patch("pipeline.LAUNCH_PROFILES", profiles),
            patch("pipeline.verify_lean_file", return_value=(True, [], "")),
            patch("pipeline.process_editorial", return_value=editorial) as review,
        ):
            with patch("pipeline.run_walk", side_effect=[[candidate], []]):
                assert run_launch(count=2, seed=1, max_attempts=5, cfg=cfg, offline=True) == 1
            assert json.loads(issue_path.read_text()) == {"issues": [prior_issue]}
            assert list((root / "results").iterdir()) == [initial]
            assert json.loads(families_path.read_text()) == {"families": {}}
            assert not review.called

            with patch(
                "pipeline.run_walk",
                side_effect=[[candidate], [candidate | {"statement_hash": "second"}]],
            ):
                assert run_launch(count=2, seed=1, max_attempts=5, cfg=cfg, offline=True) == 0
            prelaunch, launch = json.loads(issue_path.read_text())["issues"]
            assert prelaunch["number"] == 0 and prelaunch["result_ids"] == [first_id]
            assert launch["number"] == 1 and launch["launch"] and len(launch["result_ids"]) == 2
            assert json.loads(initial_meta.read_text())["issue"] == 0
            assert proof.read_text() == "theorem original : True := trivial\n"
            for result_id in launch["result_ids"]:
                result = root / "results" / result_id
                meta = json.loads((result / "meta.json").read_text())
                assert meta["issue"] == 1
                assert extract_theorem_name((result / "Result.lean").read_text()) == meta["theorem_name"]

            with patch("pipeline.run_walk") as walk:
                assert run_launch(count=2, seed=1, max_attempts=5, cfg=cfg, offline=True) == 0
                walk.assert_not_called()
            assert publish_next_issue() is None


def test_family_versioning_and_deprecation() -> None:
    state: dict = {"families": {}}
    for _ in range(49):
        res = register_families([{"family": "Kagu", "version": "1.0", "tier": "Ultra"}], state, 50)
        assert not res[0]["legacy"]
    res50 = register_families([{"family": "Kagu", "version": "1.0", "tier": "Ultra"}], state, 50)
    assert res50[0]["legacy"]
    assert state["families"]["Kagu"]["deprecated"] is True

    # Active family bumps version on issue; retired family does not
    register_families([{"family": "Lapita", "version": "2.0", "tier": "mini"}], state, 50)
    bump_family_versions_for_issue(state)
    assert state["families"]["Lapita"]["minor"] == 1
    assert state["families"]["Kagu"]["minor"] == 0


def test_axiom_parser() -> None:
    src = "import Mathlib\ntheorem akcm_2026_0001 (n : Nat) : n = n := rfl\n"
    assert extract_theorem_name(src) == "akcm_2026_0001"
    axs = parse_axioms("'akcm_2026_0001' depends on axioms: [propext, Classical.choice, Quot.sound]", "akcm_2026_0001")
    assert set(axs) == ALLOWED_AXIOMS
    assert parse_axioms("'akcm_2026_0001' does not depend on any axioms", "akcm_2026_0001") == []


def test_msc2020() -> None:
    assert section_prefix("11A05") == "11"
    assert "Number theory" in section_title("11A05")
    assert section_prefix("99Z99") == "00"


if __name__ == "__main__":
    test_blocklist()
    test_press_release_rules()
    test_press_release_uses_current_title()
    test_live_namer_leaves_title_out_of_press_body()
    test_launch_replaces_issue_only_after_full_verification()
    test_family_versioning_and_deprecation()
    test_axiom_parser()
    test_msc2020()
    print("All AKCM unit tests passed.")
