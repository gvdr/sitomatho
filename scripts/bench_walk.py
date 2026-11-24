"""Fixed benchmark for the specialist walk: timing, yield, and statement invariants."""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from typing import Any

from config import ROOT
from pipeline import LAUNCH_PROFILES
from walk_runner import WalkRun, run_walk

BENCH_SEEDS = (20261124, 20261125)
BENCH_ARGS: dict[str, Any] = dict(
    count=4,
    min_steps=3,
    max_steps=12,
    max_attempts=40,
    interdisciplinary=2.5,
    exact_heartbeats=150000,
    aesop_heartbeats=150000,
    convolute=0,
    min_proof_depth=6,
    trials_per_walk=180,
    timeout=300,
)
BENCH_DIR = ROOT / "docs" / "superpowers" / "specs" / "bench"


def check_invariants(
    candidate: dict[str, Any],
    *,
    max_lemma_repeats: int = 1,
    max_statement_size: int | None = None,
    min_concepts: int | None = None,
) -> list[str]:
    """Return the ways a candidate violates the non-triviality invariants.

    `checks` and `interest` are optional: output from before those fields existed
    is only checked for repeated lemmas.
    """
    violations: list[str] = []
    nodes = candidate.get("dependencies", {}).get("nodes", [])
    lemma_counts = Counter(node.get("lemma", node.get("id", "")) for node in nodes)
    for lemma, occurrences in lemma_counts.items():
        if occurrences > max_lemma_repeats:
            violations.append(f"lemma_repeated:{lemma}")
    checks = candidate.get("checks", {})
    if checks.get("simp_normal") is False:
        violations.append("padded")
    if checks.get("premise_reuse", 0):
        violations.append("premise_reuse")
    interest = candidate.get("interest", {})
    if max_statement_size is not None and interest.get("statement_size", 0) > max_statement_size:
        violations.append("too_large")
    if min_concepts is not None and "concepts" in interest and interest["concepts"] < min_concepts:
        violations.append("few_concepts")
    # A set used as a bare predicate prints as an unapplied `Membership.mem`; a lemma was
    # applied through the definitional unfolding of `Set`, which no reader would write.
    if "Membership.mem" in candidate.get("statement_pretty", ""):
        violations.append("unfolded_notation")
    return violations


def summarize_run(
    run: WalkRun,
    *,
    module: str,
    focus: str,
    seed: int,
    wall_seconds: float,
    max_statement_size: int | None,
    min_concepts: int | None,
) -> dict[str, Any]:
    candidates = []
    for candidate in run.candidates:
        candidates.append(
            {
                "statement_hash": candidate.get("statement_hash", ""),
                "statement_pretty": candidate.get("statement_pretty", ""),
                "interest": candidate.get("interest"),
                "lemmas": [
                    node.get("lemma", node.get("id", ""))
                    for node in candidate.get("dependencies", {}).get("nodes", [])
                ],
                "violations": check_invariants(
                    candidate, max_statement_size=max_statement_size, min_concepts=min_concepts
                ),
            }
        )
    return {
        "module": module,
        "focus": focus,
        "seed": seed,
        "wall_seconds": round(wall_seconds, 1),
        "candidates": len(candidates),
        "valid_candidates": sum(1 for c in candidates if not c["violations"]),
        "timed_out": run.timed_out,
        "complete": run.complete,
        "stats": run.stats,
        "results": candidates,
    }


def totals(runs: list[dict[str, Any]]) -> dict[str, Any]:
    wall = round(sum(r["wall_seconds"] for r in runs), 1)
    valid = sum(r["valid_candidates"] for r in runs)
    return {
        "wall_seconds": wall,
        "candidates": sum(r["candidates"] for r in runs),
        "valid_candidates": valid,
        "modules_with_valid": len({r["module"] for r in runs if r["valid_candidates"]}),
        "seconds_per_valid_candidate": round(wall / valid, 1) if valid else None,
        "violations": sum(len(c["violations"]) for r in runs for c in r["results"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Benchmark the specialist walk on fixed modules and seeds.")
    parser.add_argument("--label", required=True, help="Name of the summary file under the bench directory")
    parser.add_argument("--strict", action="store_true", help="Exit 1 when any candidate violates an invariant")
    parser.add_argument("--min-concepts", type=int, default=None)
    parser.add_argument("--max-statement-size", type=int, default=None)
    parser.add_argument("--only", default=None, help="Run only modules whose name contains this text")
    args = parser.parse_args()

    runs: list[dict[str, Any]] = []
    for module, focus in LAUNCH_PROFILES:
        if args.only and args.only not in module:
            continue
        for seed in BENCH_SEEDS:
            started = time.monotonic()
            try:
                run = run_walk(seed=seed, module=module, focus=focus, **BENCH_ARGS)
            except RuntimeError as exc:
                print(f"[bench] {module} seed {seed}: {exc}")
                run = WalkRun()
            summary = summarize_run(
                run,
                module=module,
                focus=focus,
                seed=seed,
                wall_seconds=time.monotonic() - started,
                max_statement_size=args.max_statement_size,
                min_concepts=args.min_concepts,
            )
            runs.append(summary)
            print(
                f"[bench] {module} seed {seed}: {summary['wall_seconds']}s, "
                f"{summary['candidates']} candidate(s), {summary['valid_candidates']} valid, "
                f"dominant rejection {run.stats.get('dominant_reject')}"
            )

    report = {"label": args.label, "args": BENCH_ARGS, "totals": totals(runs), "runs": runs}
    BENCH_DIR.mkdir(parents=True, exist_ok=True)
    out_path = BENCH_DIR / f"{args.label}.json"
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"[bench] totals: {report['totals']}")
    print(f"[bench] wrote {out_path.relative_to(ROOT)}")
    return 1 if args.strict and report["totals"]["violations"] else 0


if __name__ == "__main__":
    sys.exit(main())
