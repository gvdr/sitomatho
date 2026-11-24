"""Unit tests for AKCM editorial rules, axiom parser, and site helpers."""

from __future__ import annotations

import json
import random
import shutil
import subprocess
import sys
import time
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bench_walk import check_invariants
from editorial import (
    _candidate_summary_for_llm,
    _validate_press_release,
    bump_family_versions_for_issue,
    is_blocked_family,
    load_blocklist,
    process_editorial,
    register_families,
    render_editorial,
    run_decider,
    run_namer,
    scale_interest,
    screen_candidate,
)
from llm import LLMError
from msc2020 import section_prefix, section_title
from pipeline import prepare_result, publish_next_issue, run_launch, run_wander
from selection import (
    PoolEntry,
    append_candidate_log,
    log_record,
    publish_limit,
    rank_pool,
    select_and_verify,
)
from verify import ALLOWED_AXIOMS, extract_theorem_name, parse_axioms
from walk_runner import WalkRun, read_walk_output, run_walk, run_walks_parallel
from wander import TopicProfile, _mutate_knobs, derive_focus, focus_scores, mutate_profiles


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
            with patch("pipeline.run_walk", side_effect=[WalkRun(candidates=[candidate], complete=True), WalkRun(complete=True)]):
                assert run_launch(count=2, seed=1, max_attempts=5, cfg=cfg, offline=True) == 1
            assert json.loads(issue_path.read_text()) == {"issues": [prior_issue]}
            assert list((root / "results").iterdir()) == [initial]
            assert json.loads(families_path.read_text()) == {"families": {}}
            assert not review.called
            assert not (root / "state" / "candidates.jsonl").exists()

            with patch(
                "pipeline.run_walk",
                side_effect=[
                    WalkRun(candidates=[candidate], complete=True),
                    WalkRun(candidates=[candidate | {"statement_hash": "second"}], complete=True),
                ],
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


def test_wander_mutation_avoids_recent_domains_and_drifts() -> None:
    assert derive_focus("Mathlib.Combinatorics.SimpleGraph.Clique") == "Mathlib.Combinatorics.SimpleGraph"
    assert derive_focus("Mathlib.Order.Zorn") == "Mathlib.Order"

    pool = [
        TopicProfile("Mathlib.Topology.Sheaves.A", "Mathlib.Topology.Sheaves", "Topology", 40),
        TopicProfile("Mathlib.Topology.Sheaves.B", "Mathlib.Topology.Sheaves", "Topology", 35),
        TopicProfile("Mathlib.NumberTheory.Padics.A", "Mathlib.NumberTheory.Padics", "NumberTheory", 50),
        TopicProfile("Mathlib.Combinatorics.SimpleGraph.A", "Mathlib.Combinatorics.SimpleGraph", "Combinatorics", 45),
        TopicProfile("Mathlib.Probability.Martingale.A", "Mathlib.Probability.Martingale", "Probability", 40),
        TopicProfile("Mathlib.Dynamics.Ergodic.A", "Mathlib.Dynamics.Ergodic", "Dynamics", 30),
    ]
    state = {
        "history": [
            {"module": "Mathlib.Topology.Sheaves.A", "focus": "Mathlib.Topology.Sheaves", "domain": "Topology"}
        ]
    }
    with TemporaryDirectory() as empty_results:
        picked = mutate_profiles(
            seed=42,
            n_profiles=4,
            candidates=pool,
            wander_state=state,
            results_dir=Path(empty_results),
        )
    assert len(picked) == 4
    # Must include a sideways drift to the unseen sibling Sheaves.B and 3 distinct fresh domains
    assert any(p.mutation_kind == "drift" and p.module == "Mathlib.Topology.Sheaves.B" for p in picked)
    assert len({p.domain for p in picked}) == 4
    assert all(p.module != "Mathlib.Topology.Sheaves.A" for p in picked)


def test_gemini_decision_1_referee() -> None:
    meta = {
        "statement_lean": "theorem akcm_2026_0099 : True",
        "statement_hash": "expr:decisiontest",
        "steps_taken": 6,
        "namespaces": ["Topology"],
        "interdisciplinarity": 1,
        "dependencies": {"nodes": [{"id": "IsClopen.union", "kind": "mathlib"}], "edges": []},
        "novelty": {"level_1_exact_failed": True, "level_2_not_routine": True, "level_3_ratio": 4.2},
    }
    mock_answers = {
        "kind": {"choice": "Lemma", "probabilities": {"Lemma": 0.68, "Theorem": 0.22}, "confidence": 0.74},
        "importance": {"score": 3.62, "confidence": 0.85},
        "msc_section": {"choice": "54", "probabilities": {"54": 0.91}, "confidence": 0.92},
        "surprising": {"noul": 0.14, "confidence": 0.88},
        "human_cares": {"noul": 0.03, "confidence": 0.95},
    }
    with patch("editorial.gemini_decisions", return_value=mock_answers) as mock_call:
        verdict = run_decider(
            meta,
            referee_id="Referee A",
            model="gemini-decision-1",
            endpoint="https://generativelanguage.googleapis.com/v1beta/openai/",
            persona_note="",
            offline=False,
        )
    assert mock_call.called
    assert verdict["model"] == "gemini-decision-1"
    assert verdict["kind"] == "Lemma"
    assert verdict["importance"] == 4
    assert verdict["msc_code"] == "54A05"
    assert "3.62/10" in verdict["justification"]
    assert "P(surprising) = 0.14" in verdict["justification"]
    assert "P(a human mathematician cares) = 0.03" in verdict["justification"]
    assert verdict["decision_metrics"]["p_human_cares"] == 0.03


def test_read_walk_output_partial_and_missing() -> None:
    with TemporaryDirectory() as directory:
        path = Path(directory) / "walk.json"
        assert read_walk_output(path) == WalkRun()
        path.write_text("{not json", encoding="utf-8")
        assert read_walk_output(path) == WalkRun()
        path.write_text(
            json.dumps({"complete": False, "stats": {"attempts": 3}, "candidates": [{"statement_hash": "a"}]}),
            encoding="utf-8",
        )
        run = read_walk_output(path)
        assert run.candidates == [{"statement_hash": "a"}] and not run.complete
        assert run.stats["attempts"] == 3


def test_run_walk_timeout_keeps_partial_output() -> None:
    def killed_after_one_candidate(cmd, **kwargs):
        out_path = Path(cmd[cmd.index("--out") + 1])
        out_path.write_text(
            json.dumps({"complete": False, "stats": {}, "candidates": [{"statement_hash": "a"}]}),
            encoding="utf-8",
        )
        raise subprocess.TimeoutExpired(cmd, kwargs.get("timeout", 1))

    with TemporaryDirectory() as directory:
        with (
            patch("walk_runner.ROOT", Path(directory)),
            patch("walk_runner.find_lake", return_value="lake"),
            patch("walk_runner.subprocess.run", side_effect=killed_after_one_candidate),
        ):
            run = run_walk(
                seed=7, count=2, min_steps=3, max_steps=8, max_attempts=5, interdisciplinary=2.0,
                exact_heartbeats=1, aesop_heartbeats=1, convolute=0, timeout=1,
            )
    assert run.timed_out and not run.complete and len(run.candidates) == 1


def test_bench_invariants() -> None:
    def node(name: str) -> dict:
        return {"id": name, "lemma": name, "kind": "mathlib"}

    padded = {
        "dependencies": {"nodes": [node("A.u"), node("A.i"), node("A.u")]},
        "checks": {"simp_normal": False, "premise_reuse": 2},
        "interest": {"statement_size": 900, "concepts": 1},
    }
    assert check_invariants(padded, max_statement_size=400, min_concepts=3) == [
        "lemma_repeated:A.u", "padded", "premise_reuse", "too_large", "few_concepts",
    ]
    clean = {
        "dependencies": {"nodes": [node("A.u"), node("B.v")]},
        "checks": {"simp_normal": True, "premise_reuse": 0},
        "interest": {"statement_size": 120, "concepts": 3},
    }
    assert check_invariants(clean, max_statement_size=400, min_concepts=3) == []
    assert check_invariants({"dependencies": {"nodes": [node("A.u")]}}) == []


def test_screening_uses_referee_and_falls_back() -> None:
    cfg = {"llm": {"endpoint": "e", "decisions_endpoint": "d", "decider_1_model": "gemini-decision-1"}}
    candidate = {
        "statement_lean": "theorem t : True",
        "statement_hash": "h",
        "steps_taken": 5,
        "namespaces": ["Filter"],
        "dependencies": {"nodes": [], "edges": []},
        "novelty": {"level_3_ratio": 2.0},
        "interest": {"score": 22.0},
    }
    answers = {
        "kind": {"choice": "Lemma"},
        "importance": {"score": 5.4, "confidence": 0.5},
        "msc_section": {"choice": "54"},
        "surprising": {"noul": 0.2},
        "human_cares": {"noul": 0.31},
    }
    with patch("editorial.resolve_api_key", return_value="k"), patch(
        "editorial.gemini_decisions", return_value=answers
    ):
        live = screen_candidate(candidate, cfg=cfg)
    assert live["source"] == "referee_a" and live["score"] == 5.4 and live["tie_break"] == 0.31
    assert live["verdict"]["model"] == "gemini-decision-1"

    with patch("editorial.resolve_api_key", return_value="k"), patch(
        "editorial.gemini_decisions", side_effect=LLMError("down")
    ):
        failed = screen_candidate(candidate, cfg=cfg)
    assert failed == {"score": 5.5, "tie_break": 0.0, "source": "interest_score", "verdict": None}

    without_interest = {k: v for k, v in candidate.items() if k != "interest"}
    no_interest = screen_candidate(without_interest, cfg=cfg, offline=True)
    assert no_interest["score"] == 0.0 and no_interest["source"] == "interest_score"
    assert scale_interest(100.0) == 10.0 and scale_interest(-3.0) == 0.0

    readable = candidate | {"statement_pretty": "∀ {α : Type} (s : Set α), s ⊆ s"}
    summary = _candidate_summary_for_llm(readable | {"interdisciplinarity": 1})
    assert "s ⊆ s" in summary and "theorem t : True" not in summary
    assert "theorem t : True" in _candidate_summary_for_llm(candidate | {"interdisciplinarity": 1})


def test_precomputed_referee_a_is_reused() -> None:
    cfg = {
        "llm": {
            "endpoint": "e",
            "decisions_endpoint": "d",
            "decider_1_model": "gemini-decision-1",
            "decider_2_model": "m2",
            "namer_model": "m3",
            "gloss_model": "m4",
        },
        "naming": {"deprecate_after": 50, "joint_eponym_min_score": 8},
    }
    meta = {
        "statement_lean": "theorem akcm_2026_0098 : True",
        "statement_hash": "expr:reuse",
        "steps_taken": 6,
        "namespaces": ["Topology"],
        "interdisciplinarity": 1,
        "dependencies": {"nodes": [{"id": "IsClopen.union", "kind": "mathlib"}], "edges": []},
        "novelty": {"level_1_exact_failed": True, "level_2_not_routine": True, "level_3_ratio": 4.2},
    }
    verdict = {
        "referee_id": "Referee A",
        "model": "gemini-decision-1",
        "kind": "Theorem",
        "importance": 7,
        "msc_code": "54A05",
        "justification": "kept",
    }
    editorial = process_editorial(
        meta, offline=True, cfg=cfg, families_state={"families": {}}, referee_a=verdict
    )
    assert editorial["referees"][0]["justification"] == "kept"
    assert editorial["referees"][0]["model"] == "gemini-decision-1"
    assert editorial["referees"][1]["model"] == "offline-heuristic-referee"


def test_rank_select_and_log() -> None:
    def entry(tag: str, module: str, score: float, tie: float = 0.0, source: str = "referee_a") -> PoolEntry:
        profile = TopicProfile(module, "Mathlib.X", "X", 30)
        return PoolEntry(
            {"statement_hash": tag, "statement_pretty": tag},
            profile,
            1,
            {"score": score, "tie_break": tie, "source": source, "verdict": None},
        )

    pool = [
        entry("d", "M.B", 4.0),
        entry("a", "M.A", 6.0),
        entry("b", "M.A", 6.0, 0.4),
        entry("c", "M.A", 5.0),
        entry("e", "M.C", 5.5, source="interest_score"),
    ]
    ranked = rank_pool(pool)
    assert [e.candidate["statement_hash"] for e in ranked] == ["b", "a", "e", "c", "d"]

    def verify(e: PoolEntry) -> str | None:
        return None if e.candidate["statement_hash"] == "a" else e.candidate["statement_hash"]

    accepted, outcomes = select_and_verify(ranked, count=3, module_cap=1, verify=verify)
    assert [result for _, result in accepted] == ["b", "e", "d"]
    assert outcomes == {"b": "published", "a": "outranked", "e": "published", "c": "outranked", "d": "published"}

    accepted, outcomes = select_and_verify(ranked, count=2, module_cap=2, verify=verify)
    assert [result for _, result in accepted] == ["b", "e"]
    assert outcomes["a"] == "failed_verification" and outcomes["c"] == "outranked"
    assert select_and_verify([], count=3, verify=verify) == ([], {})
    assert [publish_limit(6, n) for n in (0, 1, 2, 5, 24)] == [0, 1, 1, 3, 6]

    with TemporaryDirectory() as directory:
        path = Path(directory) / "candidates.jsonl"
        records = [log_record(e, rank=i + 1, pool_size=5, outcome="outranked") for i, e in enumerate(ranked)]
        assert records[2]["source"] == "interest_score" and records[0]["rank"] == 1
        append_candidate_log(records, path=path, keep=4)
        append_candidate_log(records[:2], path=path, keep=4)
        lines = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]
        assert [line["statement_hash"] for line in lines] == ["c", "d", "b", "a"]


def test_parallel_walks_preserve_order_and_isolate_failures() -> None:
    def job(tag: str, delay: float, fail: bool = False):
        def run() -> WalkRun:
            time.sleep(delay)
            if fail:
                raise RuntimeError("boom")
            return WalkRun(candidates=[{"statement_hash": tag}], complete=True)

        return run

    runs = run_walks_parallel([job("a", 0.2), job("b", 0.0, fail=True), job("c", 0.05)], workers=3)
    assert [[c["statement_hash"] for c in r.candidates] for r in runs] == [["a"], [], ["c"]]
    assert run_walks_parallel([], workers=4) == []


def test_drift_prefers_high_scoring_focus_and_tolerates_old_history() -> None:
    pool = [
        TopicProfile("Mathlib.A.X.One", "Mathlib.A.X", "A", 40),
        TopicProfile("Mathlib.A.X.Two", "Mathlib.A.X", "A", 40),
        TopicProfile("Mathlib.B.Y.One", "Mathlib.B.Y", "B", 40),
        TopicProfile("Mathlib.B.Y.Two", "Mathlib.B.Y", "B", 40),
        TopicProfile("Mathlib.C.Z.One", "Mathlib.C.Z", "C", 40),
    ]
    history = [
        {"module": "Mathlib.A.X.One", "focus": "Mathlib.A.X", "domain": "A", "best_score": 9.0},
        {"module": "Mathlib.B.Y.One", "focus": "Mathlib.B.Y", "domain": "B", "best_score": 0.2},
        {"module": "Mathlib.C.Z.One", "focus": "Mathlib.C.Z", "domain": "C"},  # written before scores existed
    ]
    assert focus_scores({"history": history}) == {"Mathlib.A.X": 9.0, "Mathlib.B.Y": 0.2}
    drifts: list[str] = []
    with TemporaryDirectory() as empty:
        for seed in range(200):
            picked = mutate_profiles(
                seed=seed,
                n_profiles=3,
                candidates=pool,
                wander_state={"history": history},
                results_dir=Path(empty),
            )
            drifts += [p.module for p in picked if p.mutation_kind == "drift"]
    assert drifts.count("Mathlib.A.X.Two") > 3 * drifts.count("Mathlib.B.Y.Two")


def _wander_root(directory: str) -> Path:
    root = Path(directory)
    (root / "state").mkdir()
    (root / "state" / "issues.json").write_text('{"issues": []}', encoding="utf-8")
    (root / "state" / "families.json").write_text('{"families": {}}', encoding="utf-8")
    shutil.copy(Path(__file__).resolve().parent.parent / "state" / "blocklist.json", root / "state")
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.36.0", encoding="utf-8")
    return root


def test_wander_publishes_top_of_pool_and_handles_small_pool() -> None:
    cfg = {
        "journal": {"id_prefix": "AKCM"},
        "llm": {"endpoint": "e", "decider_1_model": "m1", "decider_2_model": "m2", "namer_model": "m3", "gloss_model": "m4"},
        "naming": {"deprecate_after": 50, "joint_eponym_min_score": 8},
    }
    profiles = [
        TopicProfile("Mathlib.M.A", "Mathlib.M", "M", 30),
        TopicProfile("Mathlib.M.B", "Mathlib.M", "M", 30),
    ]
    scores = {"a1": 2.0, "a2": 6.0, "a3": 5.0, "b1": 4.0}

    def candidate(tag: str) -> dict:
        return {
            "statement_hash": tag,
            "statement_lean": "theorem akcm_candidate : True",
            "statement_pretty": "True",
            "lean_file": "theorem akcm_candidate : True := trivial\n",
            "namespaces": ["Order"],
            "steps_taken": 4,
            "novelty": {"level_2_not_routine": True},
            "dependencies": {"nodes": [], "edges": []},
        }

    def walk(**kwargs) -> WalkRun:
        tags = ["a1", "a2", "a3"] if kwargs["module"] == "Mathlib.M.A" else ["b1"]
        return WalkRun(candidates=[candidate(tag) for tag in tags], complete=True)

    def screen(cand: dict, **kwargs) -> dict:
        verdict = {
            "referee_id": "Referee A", "model": "gemini-decision-1", "kind": "Lemma",
            "importance": round(scores[cand["statement_hash"]]), "msc_code": "06A05", "justification": "screened",
        }
        return {"score": scores[cand["statement_hash"]], "tie_break": 0.0, "source": "referee_a", "verdict": verdict}

    def run(root: Path, walk_fn) -> int:
        with (
            patch("pipeline.ROOT", root),
            patch("editorial.ROOT", root),
            patch("pipeline.mutate_profiles", return_value=profiles),
            patch("pipeline.run_walk", side_effect=walk_fn),
            patch("pipeline.verify_lean_file", return_value=(True, [], "")),
            patch("pipeline.screen_candidate", side_effect=screen),
        ):
            return run_wander(
                count=3, areas=2, seed=1, max_attempts=5, exact_heartbeats=1, aesop_heartbeats=1,
                allow_convolution=False, cfg=cfg, offline=True, publish_issue=False,
                pool_factor=2, workers=2,
            )

    with TemporaryDirectory() as directory:
        root = _wander_root(directory)
        assert run(root, walk) == 0
        metas = sorted(
            (json.loads(p.read_text(encoding="utf-8")) for p in (root / "results").glob("*/meta.json")),
            key=lambda m: m["id"],
        )
        assert [m["statement_hash"] for m in metas] == ["a2", "a3"]  # publish_limit(3, 4) == 2
        assert metas[0]["selection"] == {"pool_size": 4, "rank": 1, "source": "referee_a", "score": 6.0}
        assert metas[0]["editorial"]["referees"][0]["justification"] == "screened"
        log = [json.loads(line) for line in (root / "state" / "candidates.jsonl").read_text(encoding="utf-8").splitlines()]
        assert {r["statement_hash"]: r["outcome"] for r in log} == {
            "a2": "published", "a3": "published", "b1": "outranked", "a1": "outranked",
        }
        history = json.loads((root / "state" / "wander.json").read_text(encoding="utf-8"))["history"]
        assert history[0]["best_score"] == 6.0 and history[0]["published"] == 2 and history[0]["pool_size"] == 3
        assert history[1]["best_score"] == 4.0 and history[1]["published"] == 0

    with TemporaryDirectory() as directory:
        root = _wander_root(directory)
        assert run(root, lambda **kwargs: WalkRun()) == 0
        assert not (root / "results").exists() or not list((root / "results").iterdir())
        log_path = root / "state" / "candidates.jsonl"
        assert not log_path.exists() or log_path.read_text(encoding="utf-8") == ""
        history = json.loads((root / "state" / "wander.json").read_text(encoding="utf-8"))["history"]
        assert history[0]["pool_size"] == 0 and history[0]["best_score"] is None


def test_profile_knobs_and_meta_carry_interest() -> None:
    base = TopicProfile("Mathlib.Order.Zorn", "Mathlib.Order", "Order", 30)
    assert base.min_concepts == 3 and base.min_proof_depth == 4
    mutated = _mutate_knobs(base, random.Random(1), mutation_kind="explore", allow_convolution=False)
    assert mutated.min_concepts in (3, 4) and 4 <= mutated.min_proof_depth <= 6
    assert mutated.max_steps > mutated.min_proof_depth
    candidate = {
        "statement_hash": "h",
        "statement_lean": "theorem akcm_candidate : True",
        "lean_file": "theorem akcm_candidate : True := trivial\n",
        "interest": {"score": 21.5, "concepts": 4},
        "checks": {"simp_normal": True, "premise_reuse": 0},
    }
    with patch("pipeline.verify_lean_file", return_value=(True, [], "")):
        meta, _ = prepare_result(
            candidate, result_id="AKCM-2026-0099", seed=1, interdisciplinary=2.0,
            focus="Mathlib.Order", toolchain="leanprover/lean4:v4.36.0",
        )
    assert meta["interest"]["score"] == 21.5 and meta["checks"]["simp_normal"] is True


def test_walk_command_carries_specialist_knobs() -> None:
    seen: list[list[str]] = []

    def record(cmd, **kwargs):
        seen.append(cmd)
        Path(cmd[cmd.index("--out") + 1]).write_text(
            json.dumps({"complete": True, "stats": {}, "candidates": []}), encoding="utf-8"
        )
        return subprocess.CompletedProcess(cmd, 0)

    with TemporaryDirectory() as directory:
        with (
            patch("walk_runner.ROOT", Path(directory)),
            patch("walk_runner.find_lake", return_value="lake"),
            patch("walk_runner.subprocess.run", side_effect=record),
        ):
            run_walk(
                seed=7, count=2, min_steps=3, max_steps=9, max_attempts=5, interdisciplinary=2.0,
                exact_heartbeats=1, aesop_heartbeats=1, convolute=0, module="Mathlib.Order.Zorn",
                focus="Mathlib.Order", min_proof_depth=4, min_concepts=2, max_statement_size=600, keep=5,
            )
    cmd = seen[0]
    for flag, value in (("--min-concepts", "2"), ("--max-statement-size", "600"), ("--keep", "5"),
                        ("--max-lemma-repeats", "1"), ("--min-proof-depth", "4")):
        assert cmd[cmd.index(flag) + 1] == value


if __name__ == "__main__":
    test_blocklist()
    test_press_release_rules()
    test_press_release_uses_current_title()
    test_live_namer_leaves_title_out_of_press_body()
    test_launch_replaces_issue_only_after_full_verification()
    test_family_versioning_and_deprecation()
    test_axiom_parser()
    test_msc2020()
    test_wander_mutation_avoids_recent_domains_and_drifts()
    test_gemini_decision_1_referee()
    test_read_walk_output_partial_and_missing()
    test_run_walk_timeout_keeps_partial_output()
    test_bench_invariants()
    test_screening_uses_referee_and_falls_back()
    test_precomputed_referee_a_is_reused()
    test_rank_select_and_log()
    test_parallel_walks_preserve_order_and_isolate_failures()
    test_drift_prefers_high_scoring_focus_and_tolerates_old_history()
    test_wander_publishes_top_of_pool_and_handles_small_pool()
    test_profile_knobs_and_meta_carry_interest()
    test_walk_command_carries_specialist_knobs()
    print("All AKCM unit tests passed.")
