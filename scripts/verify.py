"""Standalone Lean 4 verifier & axiom checker for AKCM results."""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from config import ROOT

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def find_lake() -> str:
    if lake := shutil.which("lake"):
        return lake
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        return str(elan_lake)
    raise FileNotFoundError("Could not find `lake` on PATH or in ~/.elan/bin/lake")


def extract_theorem_name(lean_source: str) -> str:
    m = re.search(r"^\s*theorem\s+([A-Za-z0-9_']+)", lean_source, flags=re.MULTILINE)
    if not m:
        raise ValueError("No `theorem <name>` declaration found in Lean source")
    return m.group(1)


def parse_axioms(output: str, theorem_name: str) -> list[str]:
    """Parse Lean `#print axioms` output."""
    if f"'{theorem_name}' does not depend on any axioms" in output:
        return []
    m = re.search(
        rf"'{re.escape(theorem_name)}'\s+depends on axioms:\s*\[([^\]]*)\]",
        output,
        flags=re.DOTALL,
    )
    if not m:
        raise ValueError(f"Could not parse `#print axioms` output:\n{output}")
    raw = m.group(1).strip()
    if not raw:
        return []
    return [tok.strip() for tok in raw.split(",") if tok.strip()]


def verify_lean_file(lean_path: Path, *, timeout: int = 180) -> tuple[bool, list[str], str]:
    """Compile a standalone Result.lean and verify its axioms strictly."""
    source = lean_path.read_text(encoding="utf-8")
    thm_name = extract_theorem_name(source)

    # Append `#print axioms` in a temporary file inside the workspace so lake resolves Mathlib
    tmp_dir = ROOT / ".tmp"
    tmp_dir.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        dir=tmp_dir,
        delete=False,
        encoding="utf-8",
    ) as tf:
        tf.write(source.rstrip() + f"\n\n#print axioms {thm_name}\n")
        tmp_path = Path(tf.name)

    try:
        lake = find_lake()
        env = os.environ.copy()
        elan_bin = str(Path.home() / ".elan" / "bin")
        env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"
        proc = subprocess.run(
            [lake, "env", "lean", str(tmp_path)],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        combined = (proc.stdout + "\n" + proc.stderr).strip()
        if proc.returncode != 0:
            return False, [], combined

        if "sorryAx" in combined or "declaration uses 'sorry'" in combined:
            return False, ["sorryAx"], combined

        axioms = parse_axioms(combined, thm_name)
        disallowed = set(axioms) - ALLOWED_AXIOMS
        if disallowed:
            return False, axioms, f"Disallowed axioms: {sorted(disallowed)}\n{combined}"
        return True, axioms, combined
    finally:
        tmp_path.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify standalone AKCM Result.lean files.")
    parser.add_argument(
        "paths",
        nargs="*",
        help="Result.lean files or result directories (default: all results/*/Result.lean)",
    )
    args = parser.parse_args()

    targets: list[Path] = []
    if args.paths:
        for p in args.paths:
            path = Path(p)
            if path.is_dir():
                targets.append(path / "Result.lean")
            else:
                targets.append(path)
    else:
        targets = sorted((ROOT / "results").glob("*/Result.lean"))

    if not targets:
        print("No Result.lean files found to verify.")
        return 0

    failures = 0
    for target in targets:
        ok, axioms, log = verify_lean_file(target)
        status = "PASS" if ok else "FAIL"
        print(f"[{status}] {target.relative_to(ROOT)}  axioms={axioms}")
        if not ok:
            failures += 1
            print(log)

    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
