"""Re-run LLM editorial (referees, namer, gloss) on existing verified results."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from config import ROOT, load_config
from editorial import process_editorial, save_families


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Re-run LLM editorial desk on existing verified results."
    )
    parser.add_argument(
        "--issue",
        type=int,
        default=None,
        help="Only re-run results belonging to this issue number (default: all)",
    )
    parser.add_argument(
        "--reset-families",
        action="store_true",
        help="Reset state/families.json before re-naming",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="Force offline heuristic fallback",
    )
    args = parser.parse_args()

    cfg = load_config()
    if args.reset_families:
        save_families({"families": {}})

    res_root = ROOT / "results"
    count = 0
    for d in sorted(res_root.iterdir()):
        meta_path = d / "meta.json"
        if not d.is_dir() or not meta_path.exists():
            continue
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        if not meta.get("verified"):
            continue
        if args.issue is not None and meta.get("issue") != args.issue:
            continue
        print(f"[reeditorial] Processing {meta['id']}...")
        meta["editorial"] = process_editorial(meta, offline=args.offline, cfg=cfg)
        meta_path.write_text(
            json.dumps(meta, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        print(
            f"  -> {meta['editorial']['eponym']} "
            f"(mean={meta['editorial']['mean_importance']}, MSC={meta['editorial']['msc_code']})"
        )
        count += 1

    print(f"[reeditorial] Updated {count} result(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
