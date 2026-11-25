"""Rank a pool of screened candidates and publish from the top of the ranking."""

from __future__ import annotations

import json
import math
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from wander import TopicProfile


@dataclass
class PoolEntry:
    """One screened, not yet verified candidate."""

    candidate: dict[str, Any]
    profile: TopicProfile
    batch_seed: int
    screening: dict[str, Any]


def rank_pool(pool: list[PoolEntry]) -> list[PoolEntry]:
    """Order by screening score, then tie-break, then statement hash for determinism.

    Entries the referee scored come before entries ranked by the fallback interest score:
    the two scales are not comparable, and a failed referee call must not outrank real verdicts.
    """
    return sorted(
        pool,
        key=lambda e: (
            0 if e.screening.get("source") == "referee_a" else 1,
            -float(e.screening["score"]),
            -float(e.screening.get("tie_break", 0.0)),
            e.candidate.get("statement_hash", ""),
        ),
    )


Found = tuple[TopicProfile, int, dict[str, Any]]


def shortlist(found: list[Found], *, limit: int) -> list[Found]:
    """Keep at most `limit` generated candidates for the referee, by the generator's own score.

    `found` holds `(profile, batch seed, candidate)`. The interest score is a weak guide to
    what a referee prefers, so the cut is made within modules and never between them: every
    module's best candidate is kept before any module's second best. A limit of 0 keeps all.
    """
    if limit <= 0:
        return list(found)

    def score(item: Found) -> float:
        return float(item[2].get("interest", {}).get("score", 0.0))

    by_module: dict[str, list[Found]] = {}
    for item in found:
        by_module.setdefault(item[0].module, []).append(item)
    for items in by_module.values():
        items.sort(key=lambda item: (-score(item), item[2].get("statement_hash", "")))
    modules = sorted(by_module, key=lambda module: (-score(by_module[module][0]), module))
    picked: list[Found] = []
    depth = 0
    while len(picked) < limit and any(depth < len(by_module[module]) for module in modules):
        for module in modules:
            if depth < len(by_module[module]) and len(picked) < limit:
                picked.append(by_module[module][depth])
        depth += 1
    return picked


def second_opinion(
    ranked: list[PoolEntry],
    *,
    limit: int,
    ask: Callable[[PoolEntry], dict[str, Any] | None],
) -> list[PoolEntry]:
    """Have the second referee score the top `limit` entries and rank them by both scores.

    `ask` returns the second referee's verdict, or None when it could not be reached.
    Entries with both verdicts come first, ordered by the mean of the two scores; the rest
    keep their order behind them. Entries the first referee did not score are not asked
    about, since the fallback score is on another scale.
    """
    if limit <= 0:
        return ranked
    answered: list[PoolEntry] = []
    rest: list[PoolEntry] = []
    for index, entry in enumerate(ranked):
        verdict = None
        if index < limit and entry.screening.get("source") == "referee_a":
            verdict = ask(entry)
        if verdict is None:
            rest.append(entry)
            continue
        entry.screening["referee_b"] = verdict
        entry.screening["combined"] = (float(entry.screening["score"]) + float(verdict["importance"])) / 2
        answered.append(entry)
    answered.sort(
        key=lambda e: (
            -e.screening["combined"],
            -float(e.screening["score"]),
            e.candidate.get("statement_hash", ""),
        )
    )
    return answered + rest


def publish_limit(count: int, pool_size: int) -> int:
    """Publish at most half of a screened pool, so the ranking always decides something."""
    return min(count, math.ceil(pool_size / 2))


def select_and_verify(
    ranked: list[PoolEntry],
    *,
    count: int,
    module_cap: int = 2,
    verify: Callable[[PoolEntry], Any | None],
) -> tuple[list[tuple[PoolEntry, Any]], dict[str, str]]:
    """Verify down the ranking until `count` entries pass.

    `verify` returns None when standalone verification fails. An entry is skipped
    without verification once its module already has `module_cap` accepted results.
    Returns the accepted `(entry, verify result)` pairs in rank order and an outcome
    per statement hash: "published", "outranked" or "failed_verification".
    """
    accepted: list[tuple[PoolEntry, Any]] = []
    outcomes: dict[str, str] = {}
    per_module: Counter[str] = Counter()
    for entry in ranked:
        statement_hash = entry.candidate.get("statement_hash", "")
        if len(accepted) >= count or per_module[entry.profile.module] >= module_cap:
            outcomes[statement_hash] = "outranked"
            continue
        result = verify(entry)
        if result is None:
            outcomes[statement_hash] = "failed_verification"
            continue
        accepted.append((entry, result))
        per_module[entry.profile.module] += 1
        outcomes[statement_hash] = "published"
    return accepted, outcomes


def log_record(entry: PoolEntry, *, rank: int, pool_size: int, outcome: str) -> dict[str, Any]:
    candidate = entry.candidate
    return {
        "statement_hash": candidate.get("statement_hash", ""),
        "statement_pretty": candidate.get("statement_pretty", ""),
        "module": entry.profile.module,
        "focus": entry.profile.focus,
        "interest": candidate.get("interest"),
        "score": entry.screening["score"],
        "tie_break": entry.screening.get("tie_break", 0.0),
        "source": entry.screening["source"],
        "second_opinion": entry.screening.get("referee_b", {}).get("importance"),
        "rank": rank,
        "pool_size": pool_size,
        "outcome": outcome,
    }


def append_candidate_log(records: list[dict[str, Any]], *, path: Path, keep: int = 500) -> None:
    """Append JSON lines and keep only the most recent `keep` lines."""
    existing = path.read_text(encoding="utf-8").splitlines() if path.exists() else []
    lines = existing + [json.dumps(record, ensure_ascii=False) for record in records]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(line + "\n" for line in lines[-keep:]), encoding="utf-8")
