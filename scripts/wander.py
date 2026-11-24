"""Dynamic Mathlib topic discovery and evolutionary mutation for Generator A.

Instead of locking issues to a fixed list of specialist modules, this module
discovers all prebuilt Mathlib `.olean` modules across mathematical domains,
tracks recent exploration history, and mutates each run across fresh domains
and sibling neighborhoods so consecutive issues wander across mathematics.
"""

from __future__ import annotations

import json
import random
import re
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from config import ROOT

MATHLIB_SRC_ROOT = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
MATHLIB_OLEAN_ROOT = (
    ROOT / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib"
)
WANDER_STATE_PATH = ROOT / "state" / "wander.json"

# Top-level Mathlib folders that represent mathematical domains (excluding tactics/infra/basic plumbing)
ALLOWED_DOMAINS: tuple[str, ...] = (
    "Algebra",
    "AlgebraicGeometry",
    "AlgebraicTopology",
    "Analysis",
    "CategoryTheory",
    "Combinatorics",
    "Computability",
    "Condensed",
    "Dynamics",
    "FieldTheory",
    "Geometry",
    "GroupTheory",
    "InformationTheory",
    "LinearAlgebra",
    "Logic",
    "MeasureTheory",
    "ModelTheory",
    "NumberTheory",
    "Order",
    "Probability",
    "RepresentationTheory",
    "RingTheory",
    "SetTheory",
    "Topology",
)

EXCLUDED_SEGMENTS = frozenset(
    {
        "Tactic",
        "Testing",
        "Deprecated",
        "Util",
        "Meta",
        "Lean",
        "Init",
        "Notation",
        "Defs",
        "Instances",
        "Simp",
        "Attr",
    }
)

THEOREM_DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:theorem|lemma)\s+", re.MULTILINE)


@dataclass(frozen=True)
class TopicProfile:
    module: str
    focus: str
    domain: str
    theorem_count: int
    mutation_kind: str = "explore"
    min_proof_depth: int = 7
    max_steps: int = 13
    interdisciplinary: float = 2.5
    convolute: int = 0
    trials_per_walk: int = 160


def derive_focus(module: str) -> str:
    """Derive a specialist focus prefix covering a module's local Mathlib neighborhood."""
    parts = module.split(".")
    if len(parts) >= 4:
        return ".".join(parts[:3])
    if len(parts) >= 3:
        return ".".join(parts[:2])
    return module


def discover_mathlib_modules(
    *,
    src_root: Path = MATHLIB_SRC_ROOT,
    olean_root: Path = MATHLIB_OLEAN_ROOT,
    min_theorems: int = 18,
    min_bytes: int = 4500,
    max_bytes: int = 90000,
) -> list[TopicProfile]:
    """Scan prebuilt Mathlib modules for rich mathematical neighborhoods."""
    if not src_root.exists():
        return []

    check_oleans = olean_root.exists()
    discovered: list[TopicProfile] = []

    for domain in ALLOWED_DOMAINS:
        dom_dir = src_root / domain
        if not dom_dir.is_dir():
            continue
        for lean_path in sorted(dom_dir.rglob("*.lean")):
            rel = lean_path.relative_to(src_root)
            parts = list(rel.with_suffix("").parts)
            if any(seg in EXCLUDED_SEGMENTS for seg in parts):
                continue
            try:
                size = lean_path.stat().st_size
            except OSError:
                continue
            if size < min_bytes or size > max_bytes:
                continue
            if check_oleans and not (olean_root / rel.with_suffix(".olean")).exists():
                continue
            text = lean_path.read_text(encoding="utf-8", errors="ignore")
            thm_count = len(THEOREM_DECL_RE.findall(text))
            if thm_count < min_theorems:
                continue
            module = "Mathlib." + ".".join(parts)
            discovered.append(
                TopicProfile(
                    module=module,
                    focus=derive_focus(module),
                    domain=domain,
                    theorem_count=thm_count,
                )
            )
    return discovered


def load_wander_state(path: Path = WANDER_STATE_PATH) -> dict[str, Any]:
    if not path.exists():
        return {"history": []}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, dict) and isinstance(data.get("history"), list):
            return data
    except Exception:
        pass
    return {"history": []}


def save_wander_state(state: dict[str, Any], path: Path = WANDER_STATE_PATH) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    # Keep a bounded rolling memory of the last 120 explorations
    trimmed = {"history": state.get("history", [])[-120:]}
    path.write_text(json.dumps(trimmed, indent=2) + "\n", encoding="utf-8")


def collect_recent_usage(
    *,
    wander_state: dict[str, Any] | None = None,
    results_dir: Path | None = None,
) -> tuple[dict[str, int], dict[str, int], set[str], list[str]]:
    """Count domain & focus usage from past results and wander history."""
    domain_counts: dict[str, int] = defaultdict(int)
    focus_counts: dict[str, int] = defaultdict(int)
    used_modules: set[str] = set()
    recent_focuses: list[str] = []

    res_root = results_dir if results_dir is not None else (ROOT / "results")
    if res_root.exists():
        for meta_path in sorted(res_root.glob("*/meta.json")):
            try:
                meta = json.loads(meta_path.read_text(encoding="utf-8"))
            except Exception:
                continue
            if focus := meta.get("specialist_focus"):
                focus_counts[focus] += 1
                recent_focuses.append(focus)
                parts = focus.split(".")
                if len(parts) >= 2:
                    domain_counts[parts[1]] += 1
            if mod := meta.get("specialist_module"):
                used_modules.add(mod)

    state = wander_state if wander_state is not None else load_wander_state()
    for entry in state.get("history", []):
        if mod := entry.get("module"):
            used_modules.add(mod)
        if focus := entry.get("focus"):
            focus_counts[focus] += 1
            recent_focuses.append(focus)
        if dom := entry.get("domain"):
            domain_counts[dom] += 1

    return domain_counts, focus_counts, used_modules, recent_focuses


def focus_scores(wander_state: dict[str, Any]) -> dict[str, float]:
    """Best referee screening score seen so far for each focus. Unscored entries are skipped."""
    best: dict[str, float] = {}
    for entry in wander_state.get("history", []):
        focus = entry.get("focus")
        score = entry.get("best_score")
        if focus and isinstance(score, (int, float)):
            best[focus] = max(best.get(focus, float(score)), float(score))
    return best


def _order_drift_anchors(
    anchors: list[str], scores: dict[str, float], rng: random.Random
) -> list[str]:
    """Order drift anchors by weighted sampling without replacement.

    A focus the referee scored highly is tried first more often. A focus with no
    score yet gets the mean weight of the scored ones, so it is neither favoured nor starved.
    """
    known = [max(0.1, scores[f]) for f in anchors if f in scores]
    neutral = sum(known) / len(known) if known else 1.0
    weights = {f: max(0.1, scores[f]) if f in scores else neutral for f in anchors}
    remaining = list(anchors)
    ordered: list[str] = []
    while remaining:
        pick = rng.choices(remaining, weights=[weights[f] for f in remaining], k=1)[0]
        ordered.append(pick)
        remaining.remove(pick)
    return ordered


def _mutate_knobs(
    base: TopicProfile,
    rng: random.Random,
    *,
    mutation_kind: str,
    allow_convolution: bool,
    min_depth_range: tuple[int, int] = (5, 7),
) -> TopicProfile:
    """Mutate search depth, step horizon, interdisciplinarity, and optional convolution."""
    min_depth = rng.randint(min_depth_range[0], min_depth_range[1])
    max_steps = max(min_depth + 4, rng.randint(10, 15))
    interdisc = round(rng.uniform(2.0, 4.0), 1)
    # Keep very deep specialist proofs pure more often; add baroque ceremony to a slice of runs
    if allow_convolution and rng.random() < 0.45:
        convolute = rng.randint(2, 5)
    else:
        convolute = 0
    return TopicProfile(
        module=base.module,
        focus=base.focus,
        domain=base.domain,
        theorem_count=base.theorem_count,
        mutation_kind=mutation_kind,
        min_proof_depth=min_depth,
        max_steps=max_steps,
        interdisciplinary=interdisc,
        convolute=convolute,
        trials_per_walk=180,
    )


def mutate_profiles(
    *,
    seed: int,
    n_profiles: int = 4,
    candidates: list[TopicProfile] | None = None,
    wander_state: dict[str, Any] | None = None,
    results_dir: Path | None = None,
    allow_convolution: bool = True,
    min_depth_range: tuple[int, int] = (5, 7),
) -> list[TopicProfile]:
    """Select `n_profiles` diverse, mutated Mathlib specialist targets.

    Balances two mutation strategies:
    - `explore`: jump into least-visited mathematical domains and unseen focuses.
    - `drift`: step sideways from a previously visited domain/focus to a fresh sibling module.
    """
    pool = candidates if candidates is not None else discover_mathlib_modules()
    if not pool:
        return []

    rng = random.Random(seed)
    state = wander_state if wander_state is not None else load_wander_state()
    domain_counts, focus_counts, used_modules, recent_focuses = collect_recent_usage(
        wander_state=state, results_dir=results_dir
    )

    by_domain: dict[str, list[TopicProfile]] = defaultdict(list)
    by_focus: dict[str, list[TopicProfile]] = defaultdict(list)
    for prof in pool:
        by_domain[prof.domain].append(prof)
        by_focus[prof.focus].append(prof)

    chosen: list[TopicProfile] = []
    chosen_domains: set[str] = set()
    chosen_modules: set[str] = set()

    # 1. With 1 slot (if we already have history and n_profiles >= 3), do a sideways `drift`
    #    mutation from a recent focus to an unseen sibling module in that same neighborhood.
    if recent_focuses and n_profiles >= 3:
        drift_anchors = _order_drift_anchors(
            list(dict.fromkeys(reversed(recent_focuses[-12:]))), focus_scores(state), rng
        )
        for anchor in drift_anchors:
            siblings = [
                p
                for p in by_focus.get(anchor, [])
                if p.module not in used_modules and p.module not in chosen_modules
            ]
            if not siblings:
                # Try broader domain sibling if exact focus is exhausted
                parts = anchor.split(".")
                dom = parts[1] if len(parts) >= 2 else ""
                siblings = [
                    p
                    for p in by_domain.get(dom, [])
                    if p.focus != anchor and p.module not in used_modules
                ]
            if siblings:
                pick = rng.choice(siblings)
                chosen.append(
                    _mutate_knobs(
                        pick,
                        rng,
                        mutation_kind="drift",
                        allow_convolution=allow_convolution,
                        min_depth_range=min_depth_range,
                    )
                )
                chosen_domains.add(pick.domain)
                chosen_modules.add(pick.module)
                break

    # 2. Fill remaining slots by weighted sampling across least-visited distinct domains
    while len(chosen) < n_profiles:
        avail_domains = [d for d in by_domain if d not in chosen_domains]
        if not avail_domains:
            avail_domains = list(by_domain.keys())
        if not avail_domains:
            break

        # Inverse-frequency domain weighting strongly favors unvisited branches of math
        dom_weights = [1.0 / ((1 + domain_counts.get(d, 0)) ** 2) for d in avail_domains]
        dom = rng.choices(avail_domains, weights=dom_weights, k=1)[0]

        dom_pool = [p for p in by_domain[dom] if p.module not in chosen_modules]
        if not dom_pool:
            chosen_domains.add(dom)
            continue

        # Within the domain, strongly prefer unseen modules & unseen focuses, weighted by theorem richness
        mod_weights = []
        for p in dom_pool:
            seen_mod_pen = 0.08 if p.module in used_modules else 1.0
            focus_pen = 1.0 / (1 + 2 * focus_counts.get(p.focus, 0))
            richness = min(3.0, p.theorem_count / 30.0)
            mod_weights.append(seen_mod_pen * focus_pen * richness)

        pick = rng.choices(dom_pool, weights=mod_weights, k=1)[0]
        chosen.append(
            _mutate_knobs(
                pick,
                rng,
                mutation_kind="explore",
                allow_convolution=allow_convolution,
                min_depth_range=min_depth_range,
            )
        )
        chosen_domains.add(pick.domain)
        chosen_modules.add(pick.module)

    return chosen


def record_exploration(
    profiles: list[TopicProfile],
    *,
    seed: int,
    path: Path = WANDER_STATE_PATH,
    scores: dict[str, dict[str, Any]] | None = None,
) -> None:
    """Append explored profiles to the history, with their pool statistics when given.

    `scores` is keyed by module: `{"pool_size", "published", "best_score", "mean_score"}`.
    """
    state = load_wander_state(path)
    hist = state.setdefault("history", [])
    for p in profiles:
        entry = asdict(p)
        entry["seed"] = seed
        if scores is not None:
            entry.update(scores.get(p.module, {}))
        hist.append(entry)
    save_wander_state(state, path)
