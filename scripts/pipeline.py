"""End-to-end AKCM generation, verification, editorial, and issue-publishing pipeline."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

from config import ROOT, load_config
from editorial import bump_family_versions_for_issue, load_families, process_editorial, save_families
from verify import find_lake, verify_lean_file


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


def run_walk(
    *,
    seed: int,
    count: int,
    min_steps: int,
    max_steps: int,
    interdisciplinary: float,
    exact_heartbeats: int,
    aesop_heartbeats: int,
    convolute: int,
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


def main() -> int:
    parser = argparse.ArgumentParser(description="Run the AKCM theorem generation pipeline.")
    parser.add_argument("--seed", type=int, default=20261124, help="PRNG seed for Generator A")
    parser.add_argument("--count", type=int, default=12, help="Target number of gated candidates")
    parser.add_argument("--min-steps", type=int, default=3, help="Minimum walk length")
    parser.add_argument("--max-steps", type=int, default=8, help="Maximum walk length")
    parser.add_argument("--interdisciplinary", type=float, default=2.0, help="Cross-namespace weight")
    parser.add_argument("--exact-heartbeats", type=int, default=150000, help="Level 1 exact? budget")
    parser.add_argument("--aesop-heartbeats", type=int, default=150000, help="Level 2 routine budget")
    parser.add_argument("--convolute", type=int, default=3, help="Baroque proof convolution stages (0 to disable)")
    parser.add_argument("--offline", action="store_true", help="Use offline heuristic editorial fallback")
    parser.add_argument("--publish-issue", action="store_true", help="Bundle unissued results into next Issue")
    parser.add_argument("--issue-only", action="store_true", help="Only publish next issue from pending results")
    args = parser.parse_args()

    if args.issue_only:
        publish_next_issue()
        return 0

    cfg = load_config()
    year = dt.datetime.now(dt.timezone.utc).year
    seen_hashes = load_existing_hashes()
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()

    candidates = run_walk(
        seed=args.seed,
        count=args.count,
        min_steps=args.min_steps,
        max_steps=args.max_steps,
        interdisciplinary=args.interdisciplinary,
        exact_heartbeats=args.exact_heartbeats,
        aesop_heartbeats=args.aesop_heartbeats,
        convolute=args.convolute,
    )
    print(f"[pipeline] Generator A emitted {len(candidates)} gated candidates.")

    seq = next_result_number(year)
    accepted = 0
    for cand in candidates:
        stmt_hash = cand.get("statement_hash", "")
        if stmt_hash in seen_hashes:
            print(f"  [skip] Duplicate Level 0 hash {stmt_hash[:12]}")
            continue

        akcm_id = f"{cfg['journal']['id_prefix']}-{year}-{seq:04d}"
        thm_name = akcm_id.lower().replace("-", "_")
        lean_src = rewrite_theorem_name(cand["lean_file"], thm_name)

        # Verify standalone Result.lean with Lean kernel + axiom check BEFORE editorial/publishing
        tmp_lean = ROOT / ".tmp" / f"{akcm_id}.lean"
        tmp_lean.parent.mkdir(exist_ok=True)
        tmp_lean.write_text(lean_src, encoding="utf-8")
        ok, axioms, log = verify_lean_file(tmp_lean)
        tmp_lean.unlink(missing_ok=True)

        if not ok:
            print(f"  [reject] {akcm_id} failed standalone Lean verification:\n{log[:400]}")
            continue

        meta: dict[str, Any] = {
            "id": akcm_id,
            "issue": None,
            "generated_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "generator": "A",
            "seed": cand.get("seed", args.seed),
            "steps_requested": cand.get("steps_requested", 0),
            "steps_taken": cand.get("steps_taken", 0),
            "interdisciplinary_bias": args.interdisciplinary,
            "theorem_name": thm_name,
            "statement_lean": rewrite_theorem_name(cand["statement_lean"], thm_name),
            "statement_pretty": cand.get("statement_pretty", ""),
            "statement_hash": stmt_hash,
            "axioms": axioms,
            "verified": True,
            "lean_toolchain": toolchain,
            "mathlib_rev": "v4.36.0",
            "novelty": cand.get("novelty", {}),
            "namespaces": cand.get("namespaces", []),
            "interdisciplinarity": len(cand.get("namespaces", [])),
            "dependencies": cand.get("dependencies", {"nodes": [], "edges": []}),
        }

        print(f"  [verified] {akcm_id} (steps={meta['steps_taken']}, axioms={axioms}) -> running editorial...")
        meta["editorial"] = process_editorial(meta, offline=args.offline, cfg=cfg)

        out_dir = ROOT / "results" / akcm_id
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "Result.lean").write_text(lean_src, encoding="utf-8")
        (out_dir / "meta.json").write_text(
            json.dumps(meta, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )

        seen_hashes.add(stmt_hash)
        seq += 1
        accepted += 1
        print(
            f"  [saved] {akcm_id}: {meta['editorial']['eponym']} "
            f"(mean={meta['editorial']['mean_importance']}, MSC={meta['editorial']['msc_code']})"
        )

    print(f"[pipeline] Accepted and verified {accepted}/{len(candidates)} candidates.")
    if args.publish_issue and accepted > 0:
        publish_next_issue()
    return 0


if __name__ == "__main__":
    sys.exit(main())
