"""Run `lake exe walk` and read its output, including output left behind by a killed run."""

from __future__ import annotations

import json
import os
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from config import ROOT
from verify import find_lake


@dataclass
class WalkRun:
    """Candidates and statistics from one walk process."""

    candidates: list[dict[str, Any]] = field(default_factory=list)
    stats: dict[str, Any] = field(default_factory=dict)
    complete: bool = False
    timed_out: bool = False


def read_walk_output(path: Path) -> WalkRun:
    """Read a walk output file. A missing or unparsable file is an empty, incomplete run."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return WalkRun()
    if not isinstance(data, dict):
        return WalkRun()
    candidates = data.get("candidates")
    stats = data.get("stats")
    return WalkRun(
        candidates=candidates if isinstance(candidates, list) else [],
        stats=stats if isinstance(stats, dict) else {},
        complete=bool(data.get("complete", False)),
    )


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
    timeout: int = 240,
) -> WalkRun:
    """Run Generator A. A run that hits `timeout` returns what it had written so far."""
    lake = find_lake()
    out_file = ROOT / ".tmp" / f"walk_seed_{seed}.json"
    out_file.parent.mkdir(exist_ok=True)
    if out_file.exists():
        out_file.unlink()

    env = os.environ.copy()
    elan_bin = str(Path.home() / ".elan" / "bin")
    env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

    cmd = [
        lake, "exe", "walk",
        "--seed", str(seed),
        "--count", str(count),
        "--min-steps", str(min_steps),
        "--max-steps", str(max_steps),
        "--max-attempts", str(max_attempts),
        "--interdisciplinary", str(interdisciplinary),
        "--exact-heartbeats", str(exact_heartbeats),
        "--aesop-heartbeats", str(aesop_heartbeats),
        "--convolute", str(convolute),
        "--out", str(out_file),
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
    try:
        proc = subprocess.run(cmd, cwd=ROOT, env=env, timeout=timeout)
    except subprocess.TimeoutExpired:
        run = read_walk_output(out_file)
        run.timed_out = True
        print(f"[walk] Timed out after {timeout}s; kept {len(run.candidates)} candidate(s) already written.")
        return run
    if proc.returncode != 0:
        raise RuntimeError(f"`lake exe walk` failed with exit code {proc.returncode}")
    if not out_file.exists():
        raise RuntimeError(f"Expected walk output at {out_file}")
    return read_walk_output(out_file)
