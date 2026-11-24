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
    """Order by screening score, then tie-break, then statement hash for determinism."""
    return sorted(
        pool,
        key=lambda e: (
            -float(e.screening["score"]),
            -float(e.screening.get("tie_break", 0.0)),
            e.candidate.get("statement_hash", ""),
        ),
    )


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
