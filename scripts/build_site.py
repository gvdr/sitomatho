"""Static journal and Atom feed generator."""

from __future__ import annotations

import datetime as dt
import html
import json
import re
import shutil
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any
from xml.etree import ElementTree as ET

from jinja2 import Environment, FileSystemLoader, select_autoescape

from config import ROOT, load_config
from editorial import render_editorial
from msc2020 import section_prefix, section_title

SITE_DIR = ROOT / "_site"

LEAN_KEYWORDS = {
    "import", "set_option", "theorem", "lemma", "def", "by", "have", "exact",
    "fun", "forall", "let", "in", "match", "with", "if", "then", "else",
    "open", "namespace", "end", "where", "show", "from", "calc", "Prop", "Type", "Sort",
}

NS_COLORS = [
    ("#8b1e24", "#f9ecec"),
    ("#1b4d7a", "#eaf2f9"),
    ("#1d5c3a", "#eaf4ee"),
    ("#7a4b0b", "#fdf4e3"),
    ("#5b3b75", "#f3eef8"),
    ("#2a5d67", "#e9f3f5"),
]


def highlight_lean(code: str) -> str:
    """Lightweight pure-Python syntax highlighter for Lean 4 snippets."""
    lines_out: list[str] = []
    kw_re = re.compile(r"\b(" + "|".join(sorted(LEAN_KEYWORDS, key=len, reverse=True)) + r")\b")
    for raw_line in code.splitlines():
        if raw_line.lstrip().startswith("--"):
            lines_out.append(f'<span class="lk-cm">{html.escape(raw_line)}</span>')
            continue
        escaped = html.escape(raw_line)
        escaped = kw_re.sub(r'<span class="lk-kw">\1</span>', escaped)
        for sym in ("∀", "∃", "→", "↔", "λ", "≤", "≥", "≠", "∈", "⊆", "∧", "∨", "¬", "ℕ", "ℤ", "ℚ", "ℝ", "ℂ"):
            escaped = escaped.replace(sym, f'<span class="lk-op">{sym}</span>')
        lines_out.append(escaped)
    return "\n".join(lines_out)


def render_dependency_svg(deps: dict[str, Any]) -> str:
    """Render a clean inline SVG DAG of Mathlib lemmas used in a result's walk."""
    nodes = deps.get("nodes", [])
    edges = deps.get("edges", [])
    if not nodes:
        return ""

    # Assign color per namespace
    ns_map: dict[str, tuple[str, str]] = {}
    for n in nodes:
        ns = n.get("namespace", "Mathlib")
        if ns not in ns_map:
            ns_map[ns] = NS_COLORS[len(ns_map) % len(NS_COLORS)]

    # Topological layering via BFS from roots
    adj: dict[str, list[str]] = defaultdict(list)
    indeg: dict[str, int] = {n["id"]: 0 for n in nodes}
    node_ids = [n["id"] for n in nodes]
    node_set = set(node_ids)
    for e in edges:
        u, v = e.get("from", ""), e.get("to", "")
        if u in node_set and v in node_set and u != v:
            adj[u].append(v)
            indeg[v] = indeg.get(v, 0) + 1

    layer_of: dict[str, int] = {}
    queue = [nid for nid in node_ids if indeg.get(nid, 0) == 0]
    if not queue:
        queue = [node_ids[0]]
    for nid in queue:
        layer_of[nid] = 0
    while queue:
        cur = queue.pop(0)
        for nxt in adj.get(cur, []):
            new_l = layer_of[cur] + 1
            if new_l > layer_of.get(nxt, -1) and new_l <= len(nodes):
                layer_of[nxt] = new_l
                queue.append(nxt)
    for idx, nid in enumerate(node_ids):
        layer_of.setdefault(nid, idx)

    layers: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for n in nodes:
        layers[layer_of[n["id"]]].append(n)

    ordered_layers = [layers[k] for k in sorted(layers)]
    box_w = 210
    box_h = 46
    h_gap = 48
    v_gap = 22
    pad = 20

    max_rows = max(len(col) for col in ordered_layers)
    width = pad * 2 + len(ordered_layers) * box_w + max(0, len(ordered_layers) - 1) * h_gap
    height = pad * 2 + max_rows * box_h + max(0, max_rows - 1) * v_gap

    pos: dict[str, tuple[float, float]] = {}
    for col_i, col in enumerate(ordered_layers):
        col_h = len(col) * box_h + max(0, len(col) - 1) * v_gap
        start_y = (height - col_h) / 2.0
        x = pad + col_i * (box_w + h_gap)
        for row_i, n in enumerate(col):
            y = start_y + row_i * (box_h + v_gap)
            pos[n["id"]] = (x, y)

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
        f'width="{min(width, 860)}" style="max-width:100%;height:auto;font-family:var(--mono),monospace">',
        "<defs>",
        '<marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">',
        '<path d="M 0 1 L 10 5 L 0 9 z" fill="#7a7265"/>',
        "</marker>",
        "</defs>",
    ]

    # Edges
    for e in edges:
        u, v = e.get("from", ""), e.get("to", "")
        if u not in pos or v not in pos or u == v:
            continue
        x1, y1 = pos[u]
        x2, y2 = pos[v]
        sx, sy = x1 + box_w, y1 + box_h / 2
        tx, ty = x2, y2 + box_h / 2
        cx = (sx + tx) / 2
        parts.append(
            f'<path d="M {sx:.1f} {sy:.1f} C {cx:.1f} {sy:.1f}, {cx:.1f} {ty:.1f}, {tx:.1f} {ty:.1f}" '
            f'fill="none" stroke="#8a8173" stroke-width="1.4" marker-end="url(#arrow)"/>'
        )

    # Nodes
    for n in nodes:
        nid = n["id"]
        ns = n.get("namespace", "Mathlib")
        stroke, fill = ns_map[ns]
        x, y = pos[nid]
        lemma = n.get("lemma", nid)
        label = lemma if len(lemma) <= 27 else "…" + lemma[-26:]
        parts.append(
            f'<g>'
            f'<rect x="{x:.1f}" y="{y:.1f}" width="{box_w}" height="{box_h}" rx="4" '
            f'fill="{fill}" stroke="{stroke}" stroke-width="1.2"/>'
            f'<text x="{x + 10:.1f}" y="{y + 18:.1f}" font-size="10.5" font-weight="600" fill="#191815">'
            f'{html.escape(label)}</text>'
            f'<text x="{x + 10:.1f}" y="{y + 34:.1f}" font-size="9" fill="{stroke}">'
            f'{html.escape(ns)}</text>'
            f'<title>{html.escape(lemma)} ({html.escape(ns)})</title>'
            f'</g>'
        )

    parts.append("</svg>")
    return "\n".join(parts)


def load_all_results(families_state: dict[str, Any]) -> dict[str, dict[str, Any]]:
    results: dict[str, dict[str, Any]] = {}
    fams = families_state.get("families", {})
    res_root = ROOT / "results"
    if not res_root.exists():
        return results

    for d in sorted(res_root.iterdir()):
        meta_path = d / "meta.json"
        lean_path = d / "Result.lean"
        if not d.is_dir() or not meta_path.exists() or not lean_path.exists():
            continue
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        if not meta.get("verified"):
            continue
        meta["editorial"] = render_editorial(meta.get("editorial", {}))
        meta["lean_full"] = lean_path.read_text(encoding="utf-8")
        # Single-line preview for TOC
        one_line = " ".join(meta.get("statement_pretty", meta.get("statement_lean", "")).split())
        meta["statement_one_line"] = one_line
        # Check live legacy status against families.json
        ed_fams = meta.get("editorial", {}).get("families", [])
        meta["is_legacy"] = any(
            bool(fams.get(f["family"], {}).get("deprecated", f.get("legacy", False)))
            for f in ed_fams
        )
        results[meta["id"]] = meta
    return results


def build_leaderboard(
    results: dict[str, dict[str, Any]], families_state: dict[str, Any], deprecate_after: int
) -> list[dict[str, Any]]:
    totals: dict[str, float] = defaultdict(float)
    counts: dict[str, int] = defaultdict(int)
    for r in results.values():
        mean_imp = float(r.get("editorial", {}).get("mean_importance", 0.0))
        for f in r.get("editorial", {}).get("families", []):
            fam = f["family"]
            totals[fam] += mean_imp
            counts[fam] += 1

    fams = families_state.get("families", {})
    rows = []
    for fam, total in totals.items():
        info = fams.get(fam, {})
        ver = f"{info.get('major', 1)}.{info.get('minor', 0)}"
        cnt = counts[fam]
        rows.append(
            {
                "family": fam,
                "version": ver,
                "count": cnt,
                "total_importance": round(total, 1),
                "mean_importance": round(total / max(1, cnt), 2),
                "deprecated": bool(info.get("deprecated", cnt >= deprecate_after)),
            }
        )

    rows.sort(key=lambda x: (-x["total_importance"], -x["count"], x["family"]))
    max_total = max((r["total_importance"] for r in rows), default=1.0) or 1.0
    for r in rows:
        r["bar_pct"] = max(4, int(round(100.0 * r["total_importance"] / max_total)))
    return rows


def build_atom_feed(
    *,
    title: str,
    feed_id: str,
    self_url: str,
    alt_url: str,
    updated: str,
    entries: list[dict[str, Any]],
    base_url: str,
    editor: str,
) -> str:
    ns = "http://www.w3.org/2005/Atom"
    ET.register_namespace("", ns)
    feed = ET.Element(f"{{{ns}}}feed")
    ET.SubElement(feed, f"{{{ns}}}title").text = title
    ET.SubElement(feed, f"{{{ns}}}id").text = feed_id
    ET.SubElement(feed, f"{{{ns}}}updated").text = updated
    ET.SubElement(feed, f"{{{ns}}}link", {"href": self_url, "rel": "self", "type": "application/atom+xml"})
    ET.SubElement(feed, f"{{{ns}}}link", {"href": alt_url, "rel": "alternate", "type": "text/html"})
    author = ET.SubElement(feed, f"{{{ns}}}author")
    ET.SubElement(author, f"{{{ns}}}name").text = editor

    for r in entries:
        ed = r["editorial"]
        entry = ET.SubElement(feed, f"{{{ns}}}entry")
        url = f"{base_url}/results/{r['id']}/"
        ET.SubElement(entry, f"{{{ns}}}title").text = f"{ed['eponym']} ({r['id']})"
        ET.SubElement(entry, f"{{{ns}}}id").text = url
        ET.SubElement(entry, f"{{{ns}}}link", {"href": url, "rel": "alternate", "type": "text/html"})
        ET.SubElement(entry, f"{{{ns}}}updated").text = r.get("generated_at", updated)
        summary = (
            f"{ed['kind']} · Mean importance {ed['mean_importance']}/10 · MSC {ed['msc_code']}. "
            f"{ed['press_release']}"
        )
        ET.SubElement(entry, f"{{{ns}}}summary").text = summary

    ET.indent(feed, space="  ")
    return '<?xml version="1.0" encoding="utf-8"?>\n' + ET.tostring(feed, encoding="unicode") + "\n"


def group_by_msc(items: list[dict[str, Any]]) -> list[tuple[str, list[dict[str, Any]]]]:
    buckets: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for r in items:
        code = r.get("editorial", {}).get("msc_code", "00A00")
        buckets[section_prefix(code)].append(r)
    grouped: list[tuple[str, list[dict[str, Any]]]] = []
    for prefix in sorted(buckets):
        rows = sorted(
            buckets[prefix],
            key=lambda x: (-float(x["editorial"]["mean_importance"]), x["id"]),
        )
        grouped.append((section_title(prefix), rows))
    return grouped


CALIBRATION_TIERS = {
    "famous": "Classical theorems",
    "library": "Random library theorems",
    "trivial": "Trivial facts",
    "published": "The generator's own results",
}


def build_calibration_view(
    data: dict[str, Any],
    set_items: list[dict[str, Any]],
    current_statements: dict[str, str] | None = None,
) -> dict[str, Any]:
    """Shape one referee calibration run (`state/calibration.json`) for the Referees page.

    `current_statements` maps the IDs of today's results to their statements. A scored
    result is marked `current` only when its ID still carries the statement that was scored:
    results can be withdrawn and their IDs reused.
    """
    current_statements = current_statements or {}
    described = {item["tier"] + "/" + item["name"]: item for item in set_items}
    groups: dict[str, list[dict[str, Any]]] = {key: [] for key in CALIBRATION_TIERS}
    for row in data["rows"]:
        item = described.get(row["id"], {})
        answered = sorted(
            (reply for reply in row["referee_b"] if "importance" in reply),
            key=lambda reply: reply["importance"],
        )
        median = answered[len(answered) // 2] if answered else None
        referee_a = row["referee_a"]
        scores = row["b_scores"]
        groups.setdefault(row["tier"], []).append(
            {
                "name": row["name"],
                "label": item.get("label") or row["name"],
                "module": item.get("module", ""),
                "statement_html": highlight_lean(row["statement_pretty"]),
                "a_score": referee_a.get("expected_score", referee_a.get("importance")),
                "b_scores": scores,
                "b_mean": round(sum(scores) / len(scores), 2) if scores else None,
                "quote": {"score": median["importance"], "text": median["justification"]} if median else None,
                "stored_b": row.get("stored", {}).get("Referee B"),
                "current": current_statements.get(row["name"]) == row["statement_pretty"],
            }
        )
    for key, rows in groups.items():
        if key == "published":
            rows.sort(key=lambda row: row["name"])
        else:
            rows.sort(key=lambda row: -(row["b_mean"] if row["b_mean"] is not None else -1.0))
    published = groups["published"]
    return {
        "date": data.get("generated_at", ""),
        "repeats": data["repeats"],
        "referee_a_model": data["referee_a_model"],
        "referee_b_model": data["referee_b_model"],
        "mathlib_count": sum(len(rows) for key, rows in groups.items() if key != "published"),
        "tiers": [
            {"key": key, "title": title} | data["summary"][key]
            for key, title in CALIBRATION_TIERS.items()
            if key in data["summary"]
        ],
        "groups": groups,
        "published_count": len(published),
        "published_stable": sum(
            1 for row in published if row["b_scores"] and all(score == row["stored_b"] for score in row["b_scores"])
        ),
    }


def write_page(rel_path: str, content: str) -> None:
    target = SITE_DIR / rel_path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8")


def main() -> int:
    cfg = load_config()
    base_url = cfg["site"]["base_url"].rstrip("/")
    base_path = cfg["site"]["base_path"].rstrip("/")
    repo_url = cfg["site"]["repo_url"].rstrip("/")
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    lean_ver = toolchain.split(":")[-1] if ":" in toolchain else toolchain

    families_state = json.loads((ROOT / "state" / "families.json").read_text(encoding="utf-8"))
    issues_state = json.loads((ROOT / "state" / "issues.json").read_text(encoding="utf-8"))
    retractions_state = json.loads((ROOT / "state" / "retractions.json").read_text(encoding="utf-8"))

    all_results = load_all_results(families_state)
    listed_results = {rid: result for rid, result in all_results.items() if result.get("issue") != 0}
    issues = sorted(issues_state.get("issues", []), key=lambda x: x["number"], reverse=True)

    # Clean output directory
    if SITE_DIR.exists():
        shutil.rmtree(SITE_DIR)
    SITE_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copytree(ROOT / "site" / "static", SITE_DIR / "static")
    # Prevent GitHub Pages Jekyll processing
    (SITE_DIR / ".nojekyll").write_text("", encoding="utf-8")
    if custom_domain := cfg["site"].get("custom_domain", "").strip():
        (SITE_DIR / "CNAME").write_text(custom_domain + "\n", encoding="utf-8")

    env = Environment(
        loader=FileSystemLoader(str(ROOT / "site" / "templates")),
        autoescape=select_autoescape(["html", "xml"]),
    )
    calibration_path = ROOT / "state" / "calibration.json"
    calibration = (
        json.loads(calibration_path.read_text(encoding="utf-8")) if calibration_path.exists() else None
    )
    common_ctx = {
        "has_calibration": calibration is not None,
        "journal": cfg["journal"],
        "base_url": base_url,
        "base_path": base_path,
        "repo_url": repo_url,
        "lean_version": lean_ver,
        "mathlib_rev": "v4.36.0",
        "deprecate_after": cfg["naming"]["deprecate_after"],
    }

    now_iso = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    # 1. Render each Issue page + per-issue Atom feed
    issue_summaries = []
    latest_issue_html: str | None = None
    issue_tpl = env.get_template("issue.html")

    for iss in issues:
        issue_number = iss["number"]
        issue_title = "Prelaunch Archive" if issue_number == 0 else f"Issue {issue_number}"
        is_current = latest_issue_html is None and issue_number != 0
        iss_results = [all_results[rid] for rid in iss.get("result_ids", []) if rid in all_results]
        grouped = group_by_msc(iss_results)
        mean_imp = (
            round(sum(float(r["editorial"]["mean_importance"]) for r in iss_results) / len(iss_results), 1)
            if iss_results
            else 0.0
        )
        issue_summaries.append(
            {
                "number": iss["number"],
                "volume": iss.get("volume", 1),
                "date": iss["date"],
                "count": len(iss_results),
                "mean_importance": f"{mean_imp:.1f}",
            }
        )
        rendered = issue_tpl.render(
            **common_ctx,
            nav_active="current" if is_current else "issues",
            issue=iss,
            results=iss_results,
            grouped_results=grouped,
            issue_mean_importance=f"{mean_imp:.1f}",
        )
        write_page(f"issues/{iss['number']}/index.html", rendered)
        if is_current:
            latest_issue_html = rendered

        # Per-issue Atom feed
        iss_feed = build_atom_feed(
            title=f"{cfg['journal']['title']} — {issue_title}",
            feed_id=f"{base_url}/issues/{iss['number']}/feed.xml",
            self_url=f"{base_url}/issues/{iss['number']}/feed.xml",
            alt_url=f"{base_url}/issues/{iss['number']}/",
            updated=iss.get("published_at", now_iso),
            entries=iss_results,
            base_url=base_url,
            editor=cfg["journal"]["editor"],
        )
        write_page(f"issues/{iss['number']}/feed.xml", iss_feed)

    # Front page = latest issue (or empty state)
    if latest_issue_html is None:
        latest_issue_html = issue_tpl.render(
            **common_ctx,
            nav_active="current",
            issue=None,
            results=[],
            grouped_results=[],
            issue_mean_importance="0.0",
        )
    write_page("index.html", latest_issue_html)

    # 2. Issues Archive page
    write_page(
        "issues/index.html",
        env.get_template("issues_index.html").render(
            **common_ctx,
            nav_active="issues",
            issues=issue_summaries,
            total_results=len(listed_results),
        ),
    )

    # 3. Result detail pages + raw Result.lean downloads
    res_tpl = env.get_template("result.html")
    for rid, r in all_results.items():
        rendered = res_tpl.render(
            **common_ctx,
            nav_active="current",
            r=r,
            statement_html=highlight_lean(r["statement_lean"]),
            full_lean_html=highlight_lean(r["lean_full"]),
            dep_svg=render_dependency_svg(r.get("dependencies", {})),
        )
        write_page(f"results/{rid}/index.html", rendered)
        write_page(f"results/{rid}/Result.lean", r["lean_full"])

    # 4. Leaderboard
    leaderboard = build_leaderboard(listed_results, families_state, int(cfg["naming"]["deprecate_after"]))
    write_page(
        "leaderboard/index.html",
        env.get_template("leaderboard.html").render(
            **common_ctx,
            nav_active="leaderboard",
            leaderboard=leaderboard,
        ),
    )

    # 5. Retractions
    write_page(
        "retractions/index.html",
        env.get_template("retractions.html").render(
            **common_ctx,
            nav_active="retractions",
            retractions=retractions_state.get("retractions", []),
            retractions_note=retractions_state.get("note", ""),
        ),
    )

    # 6. About
    write_page(
        "about/index.html",
        env.get_template("about.html").render(
            **common_ctx,
            nav_active="about",
        ),
    )

    # 7. Referee calibration
    if calibration is not None:
        set_items = json.loads((ROOT / "scripts" / "calibration_set.json").read_text(encoding="utf-8"))["items"]
        write_page(
            "referees/index.html",
            env.get_template("referees.html").render(
                **common_ctx,
                nav_active="referees",
                cal=build_calibration_view(
                    calibration,
                    set_items,
                    current_statements={
                        rid: result.get("statement_pretty") or result.get("statement_lean", "")
                        for rid, result in all_results.items()
                    },
                ),
            ),
        )

    # 8. Site-wide Atom feed (latest 30 results)
    recent = sorted(listed_results.values(), key=lambda x: x.get("generated_at", ""), reverse=True)[:30]
    global_feed = build_atom_feed(
        title=cfg["journal"]["title"],
        feed_id=f"{base_url}/feed.xml",
        self_url=f"{base_url}/feed.xml",
        alt_url=f"{base_url}/",
        updated=recent[0].get("generated_at", now_iso) if recent else now_iso,
        entries=recent,
        base_url=base_url,
        editor=cfg["journal"]["editor"],
    )
    write_page("feed.xml", global_feed)

    print(
        f"[site] Built _site/ with {len(issues)} issue(s), {len(all_results)} result(s), "
        f"and {len(leaderboard)} ranked model families (base_path='{base_path}')."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
