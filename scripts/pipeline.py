"""End-to-end AKCM generation, verification, editorial, and issue-publishing pipeline."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import os
import re
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
    screen_candidate,
)
from selection import (
    PoolEntry,
    append_candidate_log,
    log_record,
    publish_limit,
    rank_pool,
    select_and_verify,
)
from verify import verify_lean_file
from walk_runner import WalkRun, run_walk, run_walks_parallel
from wander import TopicProfile, mutate_profiles, record_exploration

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
    specialist_module: str | None = None,
    mutation_kind: str | None = None,
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
    for key in ("proof_shape", "interest", "checks"):
        if key in candidate:
            meta[key] = candidate[key]
    if focus:
        meta["specialist_focus"] = focus
    if specialist_module:
        meta["specialist_module"] = specialist_module
    if mutation_kind:
        meta["mutation_kind"] = mutation_kind
    return meta, source


def apply_editorial(
    meta: dict[str, Any],
    *,
    cfg: dict[str, Any],
    offline: bool,
    families_state: dict[str, Any] | None = None,
    referee_a: dict[str, Any] | None = None,
) -> None:
    print(f"  [verified] {meta['id']} (steps={meta['steps_taken']}, axioms={meta['axioms']}) -> running editorial...")
    meta["editorial"] = process_editorial(
        meta, offline=offline, cfg=cfg, families_state=families_state, referee_a=referee_a
    )


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


def _walk_mutated_profile(
    profile: TopicProfile,
    *,
    batch_seed: int,
    count: int,
    max_attempts: int,
    exact_heartbeats: int,
    aesop_heartbeats: int,
) -> WalkRun:
    """Run specialist search on a mutated Mathlib profile, relaxing the concept minimum once."""
    print(
        f"[wander] ({profile.mutation_kind}) {profile.domain}: {profile.module} "
        f"[focus={profile.focus}, min_steps={profile.min_proof_depth}, min_concepts={profile.min_concepts}, "
        f"max_steps={profile.max_steps}, convolute={profile.convolute}]"
    )
    run = WalkRun()
    max_steps = max(profile.max_steps, profile.min_proof_depth + 4)
    for min_concepts in dict.fromkeys((profile.min_concepts, max(2, profile.min_concepts - 1))):
        try:
            run = run_walk(
                seed=batch_seed,
                count=count,
                min_steps=3,
                max_steps=max_steps,
                max_attempts=max_attempts,
                interdisciplinary=profile.interdisciplinary,
                exact_heartbeats=exact_heartbeats,
                aesop_heartbeats=aesop_heartbeats,
                convolute=profile.convolute,
                module=profile.module,
                focus=profile.focus,
                min_proof_depth=profile.min_proof_depth,
                trials_per_walk=profile.trials_per_walk,
                min_concepts=min_concepts,
                max_statement_size=profile.max_statement_size,
                timeout=240,
            )
        except RuntimeError as exc:
            print(f"  [wander] Walk error on {profile.module} (min_concepts={min_concepts}): {exc}")
            run = WalkRun()
        if run.candidates:
            break
    return run


def default_workers() -> int:
    """Half the CPUs: one walk process already uses more than one core and about 1.5 GB."""
    return max(1, (os.cpu_count() or 2) // 2)


def _gather_pool(
    profiles: list[TopicProfile],
    runs: list[WalkRun],
    batch_seeds: list[int],
    *,
    seen_hashes: set[str],
    cfg: dict[str, Any],
    offline: bool,
) -> list[PoolEntry]:
    """Screen every new, distinct candidate with Referee A and return the ranked pool."""
    pool: list[PoolEntry] = []
    known = set(seen_hashes)
    for profile, run, batch_seed in zip(profiles, runs, batch_seeds):
        for candidate in run.candidates:
            statement_hash = candidate.get("statement_hash", "")
            if statement_hash in known:
                continue
            known.add(statement_hash)
            screening = screen_candidate(candidate, cfg=cfg, offline=offline)
            pool.append(PoolEntry(candidate, profile, batch_seed, screening))
    ranked = rank_pool(pool)
    for rank, entry in enumerate(ranked, start=1):
        print(
            f"  [pool] #{rank} {entry.screening['score']:.2f} ({entry.screening['source']}) "
            f"{entry.profile.module} {entry.candidate.get('statement_hash', '')[:17]}"
        )
    return ranked


def _verify_down_ranking(
    ranked: list[PoolEntry],
    *,
    count: int,
    module_cap: int,
    prefix: str,
    year: int,
    first_number: int,
    toolchain: str,
    record_mutation: bool = True,
) -> tuple[list[tuple[PoolEntry, tuple[dict[str, Any], str]]], dict[str, str]]:
    """Standalone-verify candidates in rank order, assigning result IDs to those that pass."""
    passed = 0

    def verify(entry: PoolEntry) -> tuple[dict[str, Any], str] | None:
        nonlocal passed
        result = prepare_result(
            entry.candidate,
            result_id=f"{prefix}-{year}-{first_number + passed:04d}",
            seed=entry.batch_seed,
            interdisciplinary=entry.profile.interdisciplinary,
            focus=entry.profile.focus,
            toolchain=toolchain,
            specialist_module=entry.profile.module,
            mutation_kind=entry.profile.mutation_kind if record_mutation else None,
        )
        if result is not None:
            passed += 1
        return result

    return select_and_verify(ranked, count=count, module_cap=module_cap, verify=verify)


def _attach_selection(meta: dict[str, Any], entry: PoolEntry, ranked: list[PoolEntry]) -> None:
    meta["selection"] = {
        "pool_size": len(ranked),
        "rank": ranked.index(entry) + 1,
        "source": entry.screening["source"],
        "score": entry.screening["score"],
    }


def _profile_scores(
    profiles: list[TopicProfile], ranked: list[PoolEntry], outcomes: dict[str, str]
) -> dict[str, dict[str, Any]]:
    """Pool statistics per module for the wander history. Only referee scores count as scores."""
    scores: dict[str, dict[str, Any]] = {}
    for profile in profiles:
        entries = [e for e in ranked if e.profile.module == profile.module]
        refereed = [float(e.screening["score"]) for e in entries if e.screening["source"] == "referee_a"]
        scores[profile.module] = {
            "pool_size": len(entries),
            "published": sum(
                1 for e in entries if outcomes.get(e.candidate.get("statement_hash", "")) == "published"
            ),
            "best_score": max(refereed) if refereed else None,
            "mean_score": round(sum(refereed) / len(refereed), 3) if refereed else None,
        }
    return scores


def _candidate_log_records(ranked: list[PoolEntry], outcomes: dict[str, str]) -> list[dict[str, Any]]:
    return [
        log_record(
            entry,
            rank=rank,
            pool_size=len(ranked),
            outcome=outcomes.get(entry.candidate.get("statement_hash", ""), "outranked"),
        )
        for rank, entry in enumerate(ranked, start=1)
    ]


def run_wander(
    *,
    count: int,
    areas: int,
    seed: int,
    max_attempts: int,
    exact_heartbeats: int,
    aesop_heartbeats: int,
    allow_convolution: bool,
    cfg: dict[str, Any],
    offline: bool,
    publish_issue: bool,
    pool_factor: int = 4,
    workers: int = 1,
) -> int:
    """Search mutated Mathlib modules for a pool of candidates and publish the referee's top picks."""
    profiles = mutate_profiles(
        seed=seed,
        n_profiles=max(1, areas),
        results_dir=ROOT / "results",
        allow_convolution=allow_convolution,
    )
    if not profiles:
        profiles = [
            TopicProfile(module=m, focus=f, domain=m.split(".")[1], theorem_count=30)
            for m, f in LAUNCH_PROFILES[: max(1, areas)]
        ]

    year = dt.datetime.now(dt.timezone.utc).year
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    prefix = cfg["journal"]["id_prefix"]

    per_profile = math.ceil(max(1, pool_factor) * count / len(profiles))
    batch_seeds = [seed + index * 131 for index in range(len(profiles))]

    def job(profile: TopicProfile, batch_seed: int):
        return lambda: _walk_mutated_profile(
            profile,
            batch_seed=batch_seed,
            count=per_profile,
            max_attempts=max_attempts,
            exact_heartbeats=exact_heartbeats,
            aesop_heartbeats=aesop_heartbeats,
        )

    runs = run_walks_parallel(
        [job(profile, batch_seed) for profile, batch_seed in zip(profiles, batch_seeds)],
        workers=workers,
    )
    ranked = _gather_pool(
        profiles, runs, batch_seeds, seen_hashes=load_existing_hashes(), cfg=cfg, offline=offline
    )
    accepted, outcomes = _verify_down_ranking(
        ranked,
        count=publish_limit(count, len(ranked)),
        module_cap=2,
        prefix=prefix,
        year=year,
        first_number=next_result_number(year),
        toolchain=toolchain,
    )
    for entry, (meta, lean_source) in accepted:
        _attach_selection(meta, entry, ranked)
        apply_editorial(meta, cfg=cfg, offline=offline, referee_a=entry.screening["verdict"])
        save_result(meta, lean_source)

    append_candidate_log(
        _candidate_log_records(ranked, outcomes), path=ROOT / "state" / "candidates.jsonl"
    )
    record_exploration(
        profiles,
        seed=seed,
        path=ROOT / "state" / "wander.json",
        scores=_profile_scores(profiles, ranked, outcomes),
    )

    print(
        f"[wander] Published {len(accepted)} of {len(ranked)} screened candidate(s) "
        f"across {len(profiles)} module(s) (target {count})."
    )
    if publish_issue and accepted:
        publish_next_issue()
    return 0


def run_launch(
    *,
    count: int,
    seed: int,
    max_attempts: int,
    cfg: dict[str, Any],
    offline: bool,
    wander: bool = False,
    areas: int = 6,
    pool_factor: int = 4,
    workers: int = 1,
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
    prefix = cfg["journal"]["id_prefix"]

    if wander:
        profiles = mutate_profiles(
            seed=seed,
            n_profiles=max(4, areas),
            results_dir=ROOT / "results",
            allow_convolution=True,
        )
    else:
        profiles = []

    if not profiles:
        profiles = [
            TopicProfile(
                module=module,
                focus=focus,
                domain=module.split(".")[1] if "." in module else module,
                theorem_count=30,
                mutation_kind="curated",
                max_steps=14,
                interdisciplinary=2.0,
                convolute=0,
                trials_per_walk=160,
            )
            for module, focus in LAUNCH_PROFILES
        ]

    per_profile = math.ceil(max(1, pool_factor) * count / len(profiles))
    batch_seeds = [seed + index for index in range(len(profiles))]

    def job(profile: TopicProfile, batch_seed: int):
        if wander:
            return lambda: _walk_mutated_profile(
                profile,
                batch_seed=batch_seed,
                count=per_profile,
                max_attempts=max_attempts,
                exact_heartbeats=150000,
                aesop_heartbeats=150000,
            )
        return lambda: run_walk(
            seed=batch_seed,
            count=per_profile,
            min_steps=3,
            max_steps=profile.max_steps,
            max_attempts=max_attempts,
            interdisciplinary=profile.interdisciplinary,
            exact_heartbeats=150000,
            aesop_heartbeats=150000,
            convolute=profile.convolute,
            module=profile.module,
            focus=profile.focus,
            min_proof_depth=profile.min_proof_depth,
            trials_per_walk=profile.trials_per_walk,
            min_concepts=profile.min_concepts,
            max_statement_size=profile.max_statement_size,
        )

    runs = run_walks_parallel(
        [job(profile, batch_seed) for profile, batch_seed in zip(profiles, batch_seeds)],
        workers=workers,
    )
    ranked = _gather_pool(
        profiles, runs, batch_seeds, seen_hashes=load_existing_hashes(), cfg=cfg, offline=offline
    )
    # The launch issue needs its full count, so every area may contribute a little more than its share.
    accepted, outcomes = _verify_down_ranking(
        ranked,
        count=count,
        module_cap=max(2, math.ceil(count / len(profiles)) + 1),
        prefix=prefix,
        year=year,
        first_number=next_result_number(year),
        toolchain=toolchain,
        record_mutation=wander,
    )
    if len(accepted) < count:
        print(f"[launch] Verified {len(accepted)} of {count} requested results. No issue written.", file=sys.stderr)
        return 1

    families = load_families()
    verified: list[tuple[dict[str, Any], str]] = []
    for entry, (meta, source) in accepted:
        meta["issue"] = 1
        _attach_selection(meta, entry, ranked)
        apply_editorial(
            meta, cfg=cfg, offline=offline, families_state=families, referee_a=entry.screening["verdict"]
        )
        verified.append((meta, source))

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
    append_candidate_log(
        _candidate_log_records(ranked, outcomes), path=ROOT / "state" / "candidates.jsonl"
    )
    if wander:
        record_exploration(
            profiles,
            seed=seed,
            path=ROOT / "state" / "wander.json",
            scores=_profile_scores(profiles, ranked, outcomes),
        )
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
    parser.add_argument("--min-proof-depth", type=int, default=4, help="Minimum retained derivation steps for specialist search")
    parser.add_argument("--min-concepts", type=int, default=3, help="Minimum distinct concepts a specialist derivation passes through")
    parser.add_argument("--max-statement-size", type=int, default=400, help="Expression-node cap on any derived fact")
    parser.add_argument("--trials-per-walk", type=int, default=240, help="Lemma application budget per specialist walk")
    parser.add_argument("--offline", action="store_true", help="Use offline heuristic editorial fallback")
    parser.add_argument("--publish-issue", action="store_true", help="Bundle unissued results into next Issue")
    parser.add_argument("--issue-only", action="store_true", help="Only publish next issue from pending results")
    parser.add_argument("--launch-issue", action="store_true", help="Generate a full specialist batch and replace Issue 1")
    parser.add_argument("--wander", action="store_true", help="Dynamically mutate across fresh Mathlib domains & sibling modules")
    parser.add_argument("--areas", type=int, default=4, help="Number of mutated Mathlib domains to explore per --wander run")
    parser.add_argument("--pool-factor", type=int, default=4, help="Candidates screened by Referee A per published result")
    parser.add_argument("--workers", type=int, default=default_workers(), help="Walk processes to run at once")
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
            wander=args.wander,
            areas=max(4, args.areas),
            pool_factor=args.pool_factor,
            workers=args.workers,
        )

    if args.issue_only:
        publish_next_issue()
        return 0

    if args.wander and not args.module and not args.focus:
        return run_wander(
            count=args.count,
            areas=args.areas,
            seed=args.seed,
            max_attempts=args.max_attempts,
            exact_heartbeats=args.exact_heartbeats,
            aesop_heartbeats=args.aesop_heartbeats,
            allow_convolution=args.convolute > 0,
            cfg=load_config(),
            offline=args.offline,
            publish_issue=args.publish_issue,
            pool_factor=args.pool_factor,
            workers=args.workers,
        )

    if args.focus and (args.min_proof_depth < 3 or args.max_steps <= args.min_proof_depth):
        parser.error("specialist search requires 3 <= --min-proof-depth < --max-steps")
    if args.focus and args.min_concepts < 2:
        parser.error("specialist search requires --min-concepts >= 2")

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
        min_concepts=args.min_concepts,
        max_statement_size=args.max_statement_size,
    ).candidates
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
            specialist_module=args.module,
        )
        if result is None:
            continue
        meta, lean_source = result
        apply_editorial(meta, cfg=cfg, offline=args.offline)
        save_result(meta, lean_source)

        seen_hashes.add(stmt_hash)
        seq += 1
        accepted += 1

    print(f"[pipeline] Accepted and verified {accepted}/{len(candidates)} candidates.")
    if args.publish_issue and accepted > 0:
        publish_next_issue()
    return 0


if __name__ == "__main__":
    sys.exit(main())
