"""End-to-end AKCM generation, verification, editorial, and issue-publishing pipeline."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from config import ROOT, load_config
from editorial import (
    bump_family_versions_for_issue,
    load_families,
    process_editorial,
    render_editorial,
    save_families,
)
from verify import find_lake, verify_lean_file

LAUNCH_PROFILES = (
    ("Mathlib.Topology.Sheaves.MayerVietoris", "Mathlib.Topology.Sheaves"),
    ("Mathlib.RingTheory.Localization.Ideal", "Mathlib.RingTheory.Localization"),
    ("Mathlib.Algebra.Homology.ShortComplex.ShortExact", "Mathlib.Algebra.Homology.ShortComplex"),
    ("Mathlib.Order.Filter.Basic", "Mathlib.Order.Filter"),
)


def existing_result_dirs() -> list[Path]:
    res_root = ROOT / "results"
    if not res_root.exists():
        return []
    return sorted(p for p in res_root.iterdir() if p.is_dir() and (p / "meta.json").exists())


def load_existing_hashes() -> set[str]:
    hashes: set[str] = set()
    for d in existing_result_dirs():
        meta = json.loads((d / "meta.json").read_text(encoding="utf-8"))
        if h := meta.get("statement_hash"):
            hashes.add(h)
    return hashes


def next_result_number(year: int) -> int:
    prefix = f"AKCM-{year}-"
    highest = 0
    for d in existing_result_dirs():
        if d.name.startswith(prefix):
            try:
                highest = max(highest, int(d.name[len(prefix) :]))
            except ValueError:
                pass
    return highest + 1


def rewrite_theorem_name(lean_src: str, new_name: str) -> str:
    return re.sub(
        r"(^\s*theorem\s+)([A-Za-z0-9_']+)",
        rf"\g<1>{new_name}",
        lean_src,
        count=1,
        flags=re.MULTILINE,
    )


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def run_walk(
    *,
    seed: int,
    count: int,
    min_steps: int,
    max_steps: int,
    max_attempts: int,
    interdisciplinary: float,
    exact_heartbeats: int,
    aesop_heartbeats: int,
    convolute: int,
    module: str | None = None,
    focus: str | None = None,
    min_proof_depth: int = 8,
    trials_per_walk: int = 240,
) -> list[dict[str, Any]]:
    lake = find_lake()
    out_file = ROOT / ".tmp" / f"walk_seed_{seed}.json"
    out_file.parent.mkdir(exist_ok=True)
    if out_file.exists():
        out_file.unlink()

    env = os.environ.copy()
    elan_bin = str(Path.home() / ".elan" / "bin")
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

    cmd = [
        lake,
        "exe",
        "walk",
        "--seed",
        str(seed),
        "--count",
        str(count),
        "--min-steps",
        str(min_steps),
        "--max-steps",
        str(max_steps),
        "--max-attempts",
        str(max_attempts),
        "--interdisciplinary",
        str(interdisciplinary),
        "--exact-heartbeats",
        str(exact_heartbeats),
        "--aesop-heartbeats",
        str(aesop_heartbeats),
        "--convolute",
        str(convolute),
        "--out",
        str(out_file),
    ]
    if module:
        cmd.extend(["--module", module])
    if focus:
        cmd.extend([
            "--focus", focus,
            "--min-proof-depth", str(min_proof_depth),
            "--trials-per-walk", str(trials_per_walk),
        ])
    print(f"[walk] Running: {' '.join(cmd)}")
    proc = subprocess.run(cmd, cwd=ROOT, env=env)
    if proc.returncode != 0:
        raise RuntimeError(f"`lake exe walk` failed with exit code {proc.returncode}")
    if not out_file.exists():
        raise RuntimeError(f"Expected walk output at {out_file}")
    return json.loads(out_file.read_text(encoding="utf-8"))


def publish_next_issue() -> dict[str, Any] | None:
    """Group all unissued verified results into the next Issue N."""
    issues_path = ROOT / "state" / "issues.json"
    issues_state = json.loads(issues_path.read_text(encoding="utf-8"))
    issues = issues_state.setdefault("issues", [])

    unissued: list[tuple[Path, dict[str, Any]]] = []
    for d in existing_result_dirs():
        meta_path = d / "meta.json"
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        if meta.get("verified") and meta.get("issue") is None:
            unissued.append((meta_path, meta))

    if not unissued:
        print("[issue] No unissued verified results waiting to publish.")
        return None

    issue_num = (max((i["number"] for i in issues), default=0)) + 1
    today = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
    published_at = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    result_ids = []
    for meta_path, meta in unissued:
        meta["issue"] = issue_num
        meta_path.write_text(json.dumps(meta, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        result_ids.append(meta["id"])

    issue_record = {
        "number": issue_num,
        "volume": 1,
        "date": today,
        "published_at": published_at,
        "result_ids": result_ids,
    }
    issues.append(issue_record)
    issues_path.write_text(json.dumps(issues_state, indent=2) + "\n", encoding="utf-8")

    # Version numbers only go up: each issue bumps active family versions for future results
    families_state = load_families()
    bump_family_versions_for_issue(families_state)
    save_families(families_state)

    print(f"[issue] Published Issue {issue_num} ({today}) with {len(result_ids)} results.")
    return issue_record


def prepare_result(
    candidate: dict[str, Any],
    *,
    result_id: str,
    seed: int,
    interdisciplinary: float,
    focus: str | None,
    toolchain: str,
) -> tuple[dict[str, Any], str] | None:
    theorem_name = result_id.lower().replace("-", "_")
    source = rewrite_theorem_name(candidate["lean_file"], theorem_name)
    scratch = ROOT / ".tmp"
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="verify-result-", dir=scratch) as directory:
        path = Path(directory) / "Result.lean"
        path.write_text(source, encoding="utf-8")
        ok, axioms, log = verify_lean_file(path)
    if not ok:
        print(f"  [reject] {result_id} failed standalone Lean verification:\n{log[:400]}")
        return None

    namespaces = candidate.get("namespaces", [])
    meta = {
        "id": result_id,
        "issue": None,
        "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "generator": "A",
        "seed": candidate.get("seed", seed),
        "steps_requested": candidate.get("steps_requested", 0),
        "steps_taken": candidate.get("steps_taken", 0),
        "interdisciplinary_bias": interdisciplinary,
        "theorem_name": theorem_name,
        "statement_lean": rewrite_theorem_name(candidate["statement_lean"], theorem_name),
        "statement_pretty": candidate.get("statement_pretty", ""),
        "statement_hash": candidate.get("statement_hash", ""),
        "axioms": axioms,
        "verified": True,
        "lean_toolchain": toolchain,
        "mathlib_rev": "v4.36.0",
        "novelty": candidate.get("novelty", {}),
        "namespaces": namespaces,
        "interdisciplinarity": len(namespaces),
        "dependencies": candidate.get("dependencies", {"nodes": [], "edges": []}),
    }
    if "proof_shape" in candidate:
        meta["proof_shape"] = candidate["proof_shape"]
    if focus:
        meta["specialist_focus"] = focus
    return meta, source


def apply_editorial(
    meta: dict[str, Any],
    *,
    cfg: dict[str, Any],
    offline: bool,
    families_state: dict[str, Any] | None = None,
) -> None:
    print(f"  [verified] {meta['id']} (steps={meta['steps_taken']}, axioms={meta['axioms']}) -> running editorial...")
    meta["editorial"] = process_editorial(meta, offline=offline, cfg=cfg, families_state=families_state)


def save_result(meta: dict[str, Any], source: str) -> None:
    result_id = meta["id"]
    directory = ROOT / "results" / result_id
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "Result.lean").write_text(source, encoding="utf-8")
    write_json(directory / "meta.json", meta)
    print(
        f"  [saved] {result_id}: {render_editorial(meta['editorial'])['eponym']} "
        f"(mean={meta['editorial']['mean_importance']}, MSC={meta['editorial']['msc_code']})"
    )


def run_launch(
    *,
    count: int,
    seed: int,
    max_attempts: int,
    cfg: dict[str, Any],
    offline: bool,
) -> int:
    """Build a complete, verified launch issue before replacing Issue 1."""
    issues_path = ROOT / "state" / "issues.json"
    state = json.loads(issues_path.read_text(encoding="utf-8"))
    issues = state["issues"]
    first = next((issue for issue in issues if issue["number"] == 1), None)
    if first and first.get("launch"):
        print("[launch] Issue 1 is already the launch issue.")
        return 0

    year = dt.datetime.now(dt.timezone.utc).year
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    seen_hashes = load_existing_hashes()
    seq = next_result_number(year)
    prefix = cfg["journal"]["id_prefix"]
    verified: list[tuple[dict[str, Any], str]] = []
    reserve: list[tuple[dict[str, Any], str, int]] = []

    def verify_candidate(candidate: dict[str, Any], focus: str, batch_seed: int) -> None:
        statement_hash = candidate["statement_hash"]
        if statement_hash in seen_hashes:
            return
        result = prepare_result(
            candidate,
            result_id=f"{prefix}-{year}-{seq + len(verified):04d}",
            seed=batch_seed,
            interdisciplinary=2.0,
            focus=focus,
            toolchain=toolchain,
        )
        if result:
            seen_hashes.add(statement_hash)
            verified.append(result)

    # Give each area room in the issue, then use the remaining candidates if a search is sparse.
    per_area = (count + len(LAUNCH_PROFILES) - 1) // len(LAUNCH_PROFILES)
    for index, (module, focus) in enumerate(LAUNCH_PROFILES):
        batch_seed = seed + index
        candidates = run_walk(
            seed=batch_seed,
            count=count + per_area,
            min_steps=3,
            max_steps=14,
            max_attempts=max_attempts,
            interdisciplinary=2.0,
            exact_heartbeats=150000,
            aesop_heartbeats=150000,
            convolute=0,
            module=module,
            focus=focus,
            min_proof_depth=8,
            trials_per_walk=160,
        )
        candidates.sort(
            key=lambda candidate: (
                candidate["novelty"]["level_2_not_routine"],
                candidate["proof_shape"]["depth"],
            ),
            reverse=True,
        )
        limit = min(count, len(verified) + per_area)
        for candidate in candidates:
            if len(verified) < limit:
                verify_candidate(candidate, focus, batch_seed)
            else:
                reserve.append((candidate, focus, batch_seed))
        if len(verified) == count:
            break

    for candidate, focus, batch_seed in reserve:
        if len(verified) == count:
            break
        verify_candidate(candidate, focus, batch_seed)
    if len(verified) < count:
        print(f"[launch] Verified {len(verified)} of {count} requested results. No issue written.", file=sys.stderr)
        return 1

    families = load_families()
    for meta, _ in verified:
        meta["issue"] = 1
        apply_editorial(meta, cfg=cfg, offline=offline, families_state=families)

    archived_metadata = []
    for result_id in first["result_ids"] if first else []:
        path = ROOT / "results" / result_id / "meta.json"
        meta = json.loads(path.read_text(encoding="utf-8"))
        archived_metadata.append((path, meta | {"issue": 0}))

    for meta, source in verified:
        save_result(meta, source)
    for path, meta in archived_metadata:
        write_json(path, meta)

    if first:
        archive = next((issue for issue in issues if issue["number"] == 0), None)
        if archive is None:
            archive = first | {"number": 0, "result_ids": []}
            issues.append(archive)
        archive["result_ids"] = list(dict.fromkeys(archive["result_ids"] + first["result_ids"]))
        issues.remove(first)

    now = dt.datetime.now(dt.timezone.utc)
    issues.append({
        "number": 1,
        "volume": 1,
        "date": now.strftime("%Y-%m-%d"),
        "published_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "result_ids": [meta["id"] for meta, _ in verified],
        "launch": True,
    })
    state["issues"] = sorted(issues, key=lambda issue: issue["number"])
    write_json(issues_path, state)
    bump_family_versions_for_issue(families)
    save_families(families)
    print(f"[launch] Prepared Issue 1 with {count} verified results.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Run the AKCM theorem generation pipeline.")
    parser.add_argument("--seed", type=int, default=20261124, help="PRNG seed for Generator A")
    parser.add_argument("--count", type=int, default=12, help="Target number of gated candidates")
    parser.add_argument("--min-steps", type=int, default=3, help="Minimum walk length")
    parser.add_argument("--max-steps", type=int, default=8, help="Maximum walk length")
    parser.add_argument("--max-attempts", type=int, default=400, help="Maximum walk attempts")
    parser.add_argument("--interdisciplinary", type=float, default=2.0, help="Cross-namespace weight")
    parser.add_argument("--exact-heartbeats", type=int, default=150000, help="Level 1 exact? budget")
    parser.add_argument("--aesop-heartbeats", type=int, default=150000, help="Level 2 routine budget")
    parser.add_argument("--convolute", type=int, default=3, help="Baroque proof convolution stages (0 to disable)")
    parser.add_argument("--module", help="Lean module to import instead of Babel.Corpus")
    parser.add_argument("--focus", help="Mathlib module prefix for specialist seeds and conclusion symbols")
    parser.add_argument("--min-proof-depth", type=int, default=8, help="Minimum retained depth for specialist search")
    parser.add_argument("--trials-per-walk", type=int, default=240, help="Lemma application budget per specialist walk")
    parser.add_argument("--offline", action="store_true", help="Use offline heuristic editorial fallback")
    parser.add_argument("--publish-issue", action="store_true", help="Bundle unissued results into next Issue")
    parser.add_argument("--issue-only", action="store_true", help="Only publish next issue from pending results")
    parser.add_argument("--launch-issue", action="store_true", help="Generate a full specialist batch and replace Issue 1")
    args = parser.parse_args()

    if args.launch_issue:
        if args.issue_only or args.publish_issue:
            parser.error("--launch-issue cannot be combined with the regular publication flags")
        if args.count < 1 or args.max_attempts < 1:
            parser.error("launch count and maximum attempts must be positive")
        return run_launch(
            count=args.count,
            seed=args.seed,
            max_attempts=args.max_attempts,
            cfg=load_config(),
            offline=args.offline,
        )

    if args.issue_only:
        publish_next_issue()
        return 0

    if args.focus and (args.min_proof_depth < 3 or args.max_steps <= args.min_proof_depth):
        parser.error("specialist search requires 3 <= --min-proof-depth < --max-steps")

    cfg = load_config()
    year = dt.datetime.now(dt.timezone.utc).year
    seen_hashes = load_existing_hashes()
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()

    candidates = run_walk(
        seed=args.seed,
        count=args.count,
        min_steps=args.min_steps,
        max_steps=args.max_steps,
        max_attempts=args.max_attempts,
        interdisciplinary=args.interdisciplinary,
        exact_heartbeats=args.exact_heartbeats,
        aesop_heartbeats=args.aesop_heartbeats,
        convolute=args.convolute,
        module=args.module,
        focus=args.focus,
        min_proof_depth=args.min_proof_depth,
        trials_per_walk=args.trials_per_walk,
    )
    print(f"[pipeline] Generator A emitted {len(candidates)} gated candidates.")

    seq = next_result_number(year)
    accepted = 0
    for cand in candidates:
        stmt_hash = cand.get("statement_hash", "")
        if stmt_hash in seen_hashes:
            print(f"  [skip] Duplicate Level 0 hash {stmt_hash[:12]}")
            continue

        result = prepare_result(
            cand,
            result_id=f"{cfg['journal']['id_prefix']}-{year}-{seq:04d}",
            seed=args.seed,
            interdisciplinary=args.interdisciplinary,
            focus=args.focus,
            toolchain=toolchain,
        )
        if result is None:
            continue
        meta, lean_source = result
        apply_editorial(meta, cfg=cfg, offline=args.offline)
        save_result(meta, lean_source)

        seen_hashes.add(stmt_hash)
        seq += 1
        accepted += 1
        print(
            f"  [saved] {akcm_id}: {render_editorial(meta['editorial'])['eponym']} "
            f"(mean={meta['editorial']['mean_importance']}, MSC={meta['editorial']['msc_code']})"
        )

    print(f"[pipeline] Accepted and verified {accepted}/{len(candidates)} candidates.")
    if args.publish_issue and accepted > 0:
        publish_next_issue()
    return 0


if __name__ == "__main__":
    sys.exit(main())
