"""Run `lake exe walk` and read its output, including output left behind by a killed run."""

from __future__ import annotations

import json
import os
import signal
import subprocess
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

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


def run_bounded(cmd: list[str], *, cwd: Path, env: dict[str, str], timeout: int) -> int | None:
    """Run a command and return its exit code, or None when it had to be killed at `timeout`.

    The command runs in its own process group and the whole group is killed. `lake exe`
    spawns the walk binary as a child, so killing `lake` alone would leave the walk running,
    holding a core and its memory and still writing to its output file.
    """
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, start_new_session=True)
    try:
        return proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()
        return None


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
    min_concepts: int = 3,
    min_focus_steps: int = 1,
    max_lemma_repeats: int = 1,
    max_statement_size: int = 400,
    keep: int = 3,
    timeout: int = 240,
) -> WalkRun:
    """Run Generator A. A run that hits `timeout` or crashes returns what it had written so far."""
    lake = find_lake()
    # One output file per module and seed, so concurrent or successive walks never share one.
    source = (module or "corpus").replace(".", "_")
    out_file = ROOT / ".tmp" / f"walk_{source}_{seed}.json"
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
            "--min-concepts", str(min_concepts),
            "--min-focus-steps", str(min_focus_steps),
            "--max-lemma-repeats", str(max_lemma_repeats),
            "--max-statement-size", str(max_statement_size),
            "--keep", str(keep),
        ])
    print(f"[walk] Running: {' '.join(cmd)}")
    exit_code = run_bounded(cmd, cwd=ROOT, env=env, timeout=timeout)
    run = read_walk_output(out_file)
    if exit_code is None:
        run.timed_out = True
        print(f"[walk] Timed out after {timeout}s; kept {len(run.candidates)} candidate(s) already written.")
        return run
    if exit_code != 0:
        if not run.candidates:
            raise RuntimeError(f"`lake exe walk` failed with exit code {exit_code}")
        print(f"[walk] Exited with code {exit_code}; kept {len(run.candidates)} candidate(s) already written.")
        run.complete = False
        return run
    if not out_file.exists():
        raise RuntimeError(f"Expected walk output at {out_file}")
    return run


def run_walks_parallel(jobs: list[Callable[[], WalkRun]], *, workers: int) -> list[WalkRun]:
    """Run walk jobs concurrently and return their results in the order of `jobs`.

    A job that raises contributes an empty run, so one bad module cannot sink a batch.
    """
    if not jobs:
        return []

    def guarded(job: Callable[[], WalkRun]) -> WalkRun:
        try:
            return job()
        except Exception as exc:  # noqa: BLE001 - any failure of one walk is survivable
            print(f"[walk] Job failed: {exc}")
            return WalkRun()

    with ThreadPoolExecutor(max_workers=max(1, min(workers, len(jobs)))) as pool:
        return list(pool.map(guarded, jobs))
