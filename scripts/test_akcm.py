"""Unit tests for AKCM editorial rules, axiom parser, and site helpers."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from editorial import (
    _validate_press_release,
    bump_family_versions_for_issue,
    is_blocked_family,
    load_blocklist,
    register_families,
)
from msc2020 import section_prefix, section_title
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
    test_family_versioning_and_deprecation()
    test_axiom_parser()
    test_msc2020()
    print("All AKCM unit tests passed.")
