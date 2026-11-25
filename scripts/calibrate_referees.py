"""Calibrate the referees: have them score real Mathlib theorems through the production prompt.

The referees are the measuring instrument, and this script measures the instrument. It
changes no prompt and no rubric. Each theorem of `scripts/calibration_set.json` is turned
into a record shaped like a generated candidate, so that `run_decider` builds the same
request it builds for a result of the journal. Referee A is asked once per item and
Referee B several times, since Referee B answers at a high temperature and one score says
little.

    python scripts/calibrate_referees.py --out calibration.json --summary summary.md

Without `--offline` the script needs an API key and never substitutes the offline
heuristic or the other referee's model for a failed call: a failed call is recorded as an
error and left out of the statistics.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import sys
import time
from pathlib import Path
from typing import Any, Callable

from config import ROOT, load_config
from editorial import REFEREE_A_PERSONA, REFEREE_B_PERSONA, run_decider
from llm import resolve_api_key

CALIBRATION_SET = ROOT / "scripts" / "calibration_set.json"
DEFAULT_DECISIONS_ENDPOINT = "https://generativelanguage.googleapis.com/v1beta/decisions"
TIER_ORDER = ("famous", "library", "trivial", "published")


def load_calibration_set(path: Path = CALIBRATION_SET) -> list[dict[str, Any]]:
    return json.loads(path.read_text(encoding="utf-8"))["items"]


def top_namespace(name: str) -> str:
    """The namespace label the generator gives a lemma (`topNamespace` in `Babel/Util.lean`)."""
    parts = name.split(".")
    if len(parts) > 1 and parts[0] in ("Mathlib", "Batteries", "Std"):
        return parts[1]
    return parts[0]


def calibration_record(item: dict[str, Any]) -> dict[str, Any]:
    """Shape a calibration theorem like a generated candidate.

    The badges are the values every published specialist result has, because the gates
    behind them are hard gates. The remaining fields come from the theorem's real proof:
    the Mathlib lemmas it cites stand in for the steps of a walk, and the size ratio is
    that of the proof term as Mathlib stores it, without the inflation the journal adds.
    """
    lemmas = list(item["lemmas"])
    namespaces: list[str] = []
    for lemma in lemmas:
        namespace = top_namespace(lemma)
        if namespace not in namespaces:
            namespaces.append(namespace)
    statement = item["statement_pretty"]
    return {
        "id": item["tier"] + "/" + item["name"],
        "tier": item["tier"],
        "name": item["name"],
        "module": item.get("module", ""),
        "statement_pretty": statement,
        "statement_lean": statement,
        "statement_hash": hashlib.sha256(statement.encode("utf-8")).hexdigest(),
        "novelty": {
            "level_0_unseen": True,
            "level_1_exact_failed": True,
            "level_2_not_routine": True,
            "level_2_closed_by": None,
            "level_3_ratio": round(item["proof_size"] / max(1, item["statement_size"]), 2),
            "level_3_proof_size": item["proof_size"],
            "level_3_statement_size": item["statement_size"],
        },
        "steps_taken": len(lemmas),
        "namespaces": namespaces,
        "interdisciplinarity": len(namespaces),
        "dependencies": {
            "nodes": [
                {"id": str(index), "kind": "mathlib", "lemma": lemma}
                for index, lemma in enumerate(lemmas)
            ]
        },
    }


def published_records(results_dir: Path = ROOT / "results") -> list[dict[str, Any]]:
    """The journal's own results, to be scored again next to the calibration theorems."""
    records = []
    for meta_path in sorted(results_dir.glob("*/meta.json")):
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        referees = meta.get("editorial", {}).get("referees", [])
        records.append(
            meta
            | {
                "id": "published/" + meta["id"],
                "tier": "published",
                "name": meta["id"],
                "stored": {ref["referee_id"]: ref["importance"] for ref in referees},
            }
        )
    return records


def score_item(
    record: dict[str, Any],
    *,
    cfg: dict[str, Any],
    repeats: int,
    offline: bool = False,
    pause: float = 0.0,
    decide: Callable[..., dict[str, Any]] = run_decider,
) -> dict[str, Any]:
    """Ask Referee A once and Referee B `repeats` times, with the production arguments."""
    llm_cfg = cfg["llm"]
    common = {
        "endpoint": llm_cfg["endpoint"],
        "decisions_endpoint": llm_cfg.get("decisions_endpoint", DEFAULT_DECISIONS_ENDPOINT),
        "offline": offline,
    }

    def ask(referee_id: str, model: str, persona: str, bias: int) -> dict[str, Any]:
        try:
            verdict = decide(
                record,
                referee_id=referee_id,
                model=model,
                persona_note=persona,
                persona_bias=bias,
                **common,
            )
        except Exception as exc:  # noqa: BLE001 - one malformed reply must not end the run
            return {"error": f"{type(exc).__name__}: {exc}"}
        finally:
            if pause > 0:
                time.sleep(pause)
        reply = {
            "model": verdict.get("model", model),
            "importance": verdict["importance"],
            "kind": verdict.get("kind"),
            "justification": verdict.get("justification", ""),
        }
        expected = verdict.get("decision_metrics", {}).get("expected_score")
        if expected is not None:
            reply["expected_score"] = expected
        return reply

    referee_a = ask("Referee A", llm_cfg["decider_1_model"], REFEREE_A_PERSONA, 1)
    referee_b = [
        ask("Referee B", llm_cfg["decider_2_model"], REFEREE_B_PERSONA, -1) for _ in range(repeats)
    ]
    row = {
        "id": record["id"],
        "tier": record["tier"],
        "name": record["name"],
        "statement_pretty": record.get("statement_pretty") or record.get("statement_lean", ""),
        "referee_a": referee_a,
        "referee_b": referee_b,
        "b_scores": [reply["importance"] for reply in referee_b if "importance" in reply],
    }
    if "stored" in record:
        row["stored"] = record["stored"]
    return row


def _a_score(row: dict[str, Any]) -> float | None:
    reply = row["referee_a"]
    if "importance" not in reply:
        return None
    return float(reply.get("expected_score", reply["importance"]))


def summarise(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    """Statistics by tier. Referee B's score for an item is the mean of its repeats.

    `b_noise_sd` is the pooled standard deviation of Referee B's repeats on one item: how
    much its score moves when nothing about the theorem changes.
    """
    summary: dict[str, dict[str, Any]] = {}
    tiers = [tier for tier in TIER_ORDER if any(row["tier"] == tier for row in rows)]
    tiers += sorted({row["tier"] for row in rows} - set(tiers))
    for tier in tiers:
        members = [row for row in rows if row["tier"] == tier]
        a_scores = [score for row in members if (score := _a_score(row)) is not None]
        b_means = [statistics.fmean(row["b_scores"]) for row in members if row["b_scores"]]
        variances = [
            statistics.variance(row["b_scores"]) for row in members if len(row["b_scores"]) > 1
        ]
        summary[tier] = {
            "n": len(members),
            "scored": len(b_means),
            "a_mean": round(statistics.fmean(a_scores), 2) if a_scores else None,
            "b_mean": round(statistics.fmean(b_means), 2) if b_means else None,
            "b_median": round(statistics.median(b_means), 2) if b_means else None,
            "b_min": round(min(b_means), 2) if b_means else None,
            "b_max": round(max(b_means), 2) if b_means else None,
            "b_noise_sd": round(statistics.fmean(variances) ** 0.5, 2) if variances else None,
        }
    return summary


def _cell(value: float | None) -> str:
    return "n/a" if value is None else f"{value:.2f}"


def render_markdown(rows: list[dict[str, Any]], summary: dict[str, dict[str, Any]]) -> str:
    lines = [
        "## Referee calibration",
        "",
        "| Tier | Items | Scored by B | Referee A mean | Referee B mean | B median | B lowest | B highest | B noise SD |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for tier, stats in summary.items():
        lines.append(
            f"| {tier} | {stats['n']} | {stats['scored']} | {_cell(stats['a_mean'])} | "
            f"{_cell(stats['b_mean'])} | {_cell(stats['b_median'])} | {_cell(stats['b_min'])} | "
            f"{_cell(stats['b_max'])} | {_cell(stats['b_noise_sd'])} |"
        )
    lines += ["", "| Item | Referee A | Referee B scores | Statement |", "|---|---|---|---|"]

    def order(row: dict[str, Any]) -> tuple[int, float]:
        tier_rank = list(summary).index(row["tier"])
        mean = statistics.fmean(row["b_scores"]) if row["b_scores"] else -1.0
        return (tier_rank, -mean)

    for row in sorted(rows, key=order):
        scores = ", ".join(str(score) for score in row["b_scores"]) or "n/a"
        failed = len(row["referee_b"]) - len(row["b_scores"])
        if failed:
            scores += f" ({failed} failed)"
        if "stored" in row and "Referee B" in row["stored"]:
            scores += f" (stored {row['stored']['Referee B']})"
        statement = " ".join(row["statement_pretty"].split())
        if len(statement) > 110:
            statement = statement[:107] + "..."
        statement = statement.replace("|", "\\|")
        lines.append(f"| {row['id']} | {_cell(_a_score(row))} | {scores} | `{statement}` |")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, required=True, help="Where to write the scores as JSON")
    parser.add_argument("--summary", type=Path, default=None, help="Append the Markdown summary to this file")
    parser.add_argument("--repeats", type=int, default=3, help="Referee B calls per item")
    parser.add_argument("--pause", type=float, default=0.0, help="Seconds to wait after each call")
    parser.add_argument("--limit", type=int, default=None, help="Score only the first N items")
    parser.add_argument("--skip-published", action="store_true", help="Leave out the journal's own results")
    parser.add_argument("--offline", action="store_true", help="Use the offline heuristic (plumbing test only)")
    args = parser.parse_args(argv)

    if not args.offline and resolve_api_key() is None:
        print("No API key found. Calibration needs the live referees; nothing was written.", file=sys.stderr)
        return 1

    cfg = load_config()
    records = [calibration_record(item) for item in load_calibration_set()]
    if not args.skip_published:
        records += published_records()
    if args.limit is not None:
        records = records[: args.limit]

    rows = []
    for index, record in enumerate(records, start=1):
        row = score_item(record, cfg=cfg, repeats=args.repeats, offline=args.offline, pause=args.pause)
        rows.append(row)
        print(f"[{index}/{len(records)}] {row['id']}: A={_cell(_a_score(row))} B={row['b_scores']}", flush=True)

    if not args.offline and not any(row["b_scores"] for row in rows):
        print("Referee B answered no call; nothing was written.", file=sys.stderr)
        return 1

    summary = summarise(rows)
    args.out.write_text(
        json.dumps(
            {
                "offline": args.offline,
                "repeats": args.repeats,
                "referee_a_model": cfg["llm"]["decider_1_model"],
                "referee_b_model": cfg["llm"]["decider_2_model"],
                "summary": summary,
                "rows": rows,
            },
            indent=2,
            ensure_ascii=False,
        )
        + "\n",
        encoding="utf-8",
    )
    text = render_markdown(rows, summary)
    print(text)
    if args.summary is not None:
        with args.summary.open("a", encoding="utf-8") as handle:
            handle.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
