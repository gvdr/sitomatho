"""Editorial pipeline: two Deciders (referees), blocklisted Namer, and Unverified Gloss."""

from __future__ import annotations

import hashlib
import json
import random
import re
from pathlib import Path
from typing import Any

from config import ROOT, load_config
from llm import LLMError, chat_completion, extract_json, gemini_decisions, resolve_api_key
from msc2020 import MSC_SECTIONS, section_prefix

VALID_KINDS = ("Theorem", "Lemma", "Corollary", "Proposition")
ANNOUNCEMENT = "Today we are proud to announce "
REFEREE_A_PERSONA = (
    "You are a formalist inclined to reward non-routine proof depth and cross-namespace synthesis."
)
REFEREE_B_PERSONA = (
    "You are a skeptical classical mathematician who is hard to impress and suspicious of "
    "artificial hypotheses."
)

# Curated fallback invented families (all verified absent from blocklist)
FALLBACK_FAMILIES = [
    "Kagu",
    "Cassowary",
    "Noumenon",
    "Aletheia",
    "Lapita",
    "Tui",
    "Kakapo",
    "Hoatzin",
    "Quetzal",
    "Albatross",
    "Orogen",
    "Chiaroscuro",
    "Pumice",
    "Sirocco",
    "Heliodor",
    "Boreal",
    "Tephra",
    "Nacre",
    "Gnomon",
    "Caldera",
    "Rhea",
    "Takahe",
    "Petrel",
    "Kestrel",
]
FALLBACK_TIERS = [
    "Ultra",
    "Instruct",
    "mini-high",
    "Turbo",
    "405B-preview-1123",
    "Pro",
    "Reasoning",
    "Lite",
    "Max",
    "70B-Base",
    "Thinking",
]


def load_blocklist() -> set[str]:
    path = ROOT / "state" / "blocklist.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    blocked: set[str] = set()
    for group in data.values():
        for name in group:
            blocked.add(normalize_token(name))
    return blocked


def normalize_token(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())


def is_blocked_family(family: str, blocklist: set[str]) -> bool:
    norm = normalize_token(family)
    if not norm or len(norm) < 3 or not family[0].isalpha():
        return True
    if norm in blocklist:
        return True
    # Also guard against trivial suffixing of blocked real model/mathematician names
    for b in blocklist:
        if len(b) >= 4 and (norm == b or norm.startswith(b) or b in norm):
            return True
    return False


def load_families() -> dict[str, Any]:
    path = ROOT / "state" / "families.json"
    if not path.exists():
        return {"families": {}}
    return json.loads(path.read_text(encoding="utf-8"))


def save_families(data: dict[str, Any]) -> None:
    path = ROOT / "state" / "families.json"
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def bump_family_versions_for_issue(families_state: dict[str, Any]) -> None:
    """Bump every active family's minor version when publishing an issue."""
    for fam in families_state.get("families", {}).values():
        if not fam.get("deprecated", False):
            fam["minor"] = int(fam.get("minor", 0)) + 1
            if fam["minor"] >= 10:
                fam["major"] = int(fam.get("major", 1)) + 1
                fam["minor"] = 0


def format_version(fam: dict[str, Any]) -> str:
    return f"{fam.get('major', 1)}.{fam.get('minor', 0)}"


def _load_prompt(name: str) -> str:
    return (ROOT / "prompts" / f"{name}.md").read_text(encoding="utf-8")


def _walk_lemmas(meta: dict[str, Any]) -> list[str]:
    nodes = meta.get("dependencies", {}).get("nodes", [])
    return [node.get("lemma", node["id"]) for node in nodes if node.get("kind") == "mathlib"]


def _readable_statement(meta: dict[str, Any]) -> str:
    """The statement as a mathematician would read it.

    `statement_lean` is printed fully explicit for specialist results so that the standalone
    file re-elaborates; the editorial desk reads the pretty form when the record has one.
    """
    return meta.get("statement_pretty") or meta["statement_lean"]


def _candidate_summary_for_llm(meta: dict[str, Any]) -> str:
    nov = meta.get("novelty", {})
    ns = ", ".join(meta.get("namespaces", [])) or "Core"
    lemmas = _walk_lemmas(meta)
    return (
        f"Lean statement:\n```lean\n{_readable_statement(meta)}\n```\n\n"
        f"Novelty badges:\n"
        f"- Level 0 (Unseen hash): {nov.get('level_0_unseen', True)}\n"
        f"- Level 1 (Not a lookup — `exact?` failed): {nov.get('level_1_exact_failed', True)}\n"
        f"- Level 2 (Not routine — `aesop`/`simp`/`omega` failed): {nov.get('level_2_not_routine', False)}"
        f" (closed_by: {nov.get('level_2_closed_by')})\n"
        f"- Level 3 (Proof/statement ratio after shrinking): {nov.get('level_3_ratio', 1.0):.2f} "
        f"(proof={nov.get('level_3_proof_size', 0)}, stmt={nov.get('level_3_statement_size', 0)})\n"
        f"- Walk length: {meta.get('steps_taken', 0)} steps\n"
        f"- Mathlib namespaces touched ({meta.get('interdisciplinarity', 0)}): {ns}\n"
        f"- Mathlib lemmas used: {', '.join(lemmas[:15])}\n"
    )


def _guess_msc_from_namespaces(namespaces: list[str]) -> str:
    joined = " ".join(namespaces).lower()
    mapping = [
        ("nat", "11A05"),
        ("int", "11A05"),
        ("prime", "11A41"),
        ("finset", "05A10"),
        ("list", "05A05"),
        ("multiset", "05A10"),
        ("set", "03E20"),
        ("order", "06A06"),
        ("lattice", "06B05"),
        ("group", "20A05"),
        ("monoid", "20M10"),
        ("ring", "13A02"),
        ("field", "12F05"),
        ("module", "13C05"),
        ("linear", "15A03"),
        ("matrix", "15A24"),
        ("real", "26A06"),
        ("topology", "54A05"),
        ("continuous", "54C05"),
        ("filter", "54A20"),
        ("metric", "54E35"),
        ("measure", "28A05"),
        ("category", "18A05"),
        ("polynomial", "13B25"),
        ("complex", "30A05"),
        ("rat", "11A99"),
        ("function", "03E20"),
        ("logic", "03B05"),
    ]
    for key, code in mapping:
        if key in joined:
            return code
    return "03B05"


def _offline_referee(
    meta: dict[str, Any], referee_id: str, persona_bias: int
) -> dict[str, Any]:
    """Deterministic fallback referee when offline / no API key is configured."""
    rng = random.Random(
        int(hashlib.sha256(f"{meta['statement_hash']}:{referee_id}".encode()).hexdigest()[:8], 16)
    )
    nov = meta.get("novelty", {})
    ratio = float(nov.get("level_3_ratio", 1.5))
    not_routine = bool(nov.get("level_2_not_routine", False))
    interdisc = int(meta.get("interdisciplinarity", 1))
    steps = int(meta.get("steps_taken", 3))

    base = 3 + (2 if not_routine else 0) + min(2, int(ratio // 2)) + min(2, interdisc - 1)
    score = max(0, min(10, base + persona_bias + rng.randint(-2, 2)))

    if score >= 8:
        kind = "Theorem"
    elif score >= 6:
        kind = rng.choice(["Theorem", "Proposition"])
    elif score >= 4:
        kind = rng.choice(["Proposition", "Lemma"])
    else:
        kind = rng.choice(["Lemma", "Corollary"])

    msc = _guess_msc_from_namespaces(meta.get("namespaces", []))
    ns_str = ", ".join(meta.get("namespaces", [])[:3]) or "core foundations"
    if persona_bias >= 0:
        just = (
            f"The {steps}-step synthesis across {ns_str} resists single-lemma lookup and yields a "
            f"proof-to-statement ratio of {ratio:.2f}, meriting archival as a {kind.lower()}. "
            f"While its immediate utility outside the present formal context remains speculative, "
            f"the structural coupling of hypotheses is unexpectedly persistent."
        )
    else:
        just = (
            f"Although the statement clears the Level 1 lookup gate across {ns_str}, the conclusion "
            f"reads primarily as an accidental consequence of chaining {steps} library facts. "
            f"I recommend publication solely as a {kind.lower()} of modest significance ({score}/10), "
            f"noting that the kernel's indifference to mathematical taste is on full display."
        )

    return {
        "referee_id": referee_id,
        "model": "offline-heuristic-referee",
        "kind": kind,
        "importance": score,
        "msc_code": msc,
        "justification": just,
    }


DECISION_IMPORTANCE_LEVELS: list[str] = [
    "0: Completely vacuous, trivial, or redundant bookkeeping tautology.",
    "1: Barely non-trivial restatement of a single basic fact.",
    "2: Mechanical consequence of combining two routine definitions.",
    "3: Minor technical observation with very narrow artificial hypotheses.",
    "4: Modest auxiliary lemma of limited standalone interest.",
    "5: Respectable technical proposition within a specialized subfield.",
    "6: Non-trivial structural result with coherent hypotheses and nontrivial proof depth.",
    "7: Solid theorem connecting distinct concepts in a meaningful way.",
    "8: Strong, memorable theorem that a specialist would gladly cite.",
    "9: Major unifying theorem with broad cross-disciplinary reach.",
    "10: Landmark mathematical breakthrough of enduring foundational importance.",
]

DECISION_MSC_CHOICES: dict[str, str] = {
    "03": "Mathematical logic, foundations, set theory",
    "05": "Combinatorics, graphs, matroids, finite sets",
    "06": "Order, lattices, ordered algebraic structures, filters",
    "11": "Number theory, primes, p-adics, algebraic number fields",
    "12": "Field theory and polynomials",
    "13": "Commutative rings, ideals, localization",
    "14": "Algebraic geometry, schemes, varieties",
    "15": "Linear and multilinear algebra, matrices",
    "18": "Category theory, homological algebra, sheaves, condensed sets",
    "20": "Group theory and representation theory",
    "26": "Real functions and calculus",
    "28": "Measure theory and integration",
    "37": "Dynamical systems and ergodic theory",
    "46": "Functional analysis, Banach/Hilbert spaces, distributions",
    "51": "Geometry and convex geometry",
    "54": "General topology, metric spaces, connectedness",
    "55": "Algebraic topology and homotopy",
    "60": "Probability theory and stochastic processes",
    "68": "Computer science and computability",
    "94": "Information and coding theory",
}


def _run_decision_model_referee(
    meta: dict[str, Any],
    *,
    referee_id: str,
    model: str,
    decisions_endpoint: str,
) -> dict[str, Any]:
    """Score a theorem via Gemini Decisions API (`gemini-decision-1`, zero output tokens)."""
    questions: dict[str, Any] = {
        "kind": {
            "type": "choice",
            "instructions": "Classify this formally verified Lean 4 result into a mathematical publication category.",
            "criteria": {
                "Theorem": "A substantial standalone mathematical result with nontrivial depth.",
                "Proposition": "A solid intermediate mathematical statement worth recording.",
                "Lemma": "An auxiliary technical stepping stone with narrow hypotheses.",
                "Corollary": "An immediate or specialized consequence of existing results.",
            },
        },
        "importance": {
            "type": "score",
            "instructions": "Rate the genuine mathematical importance of this Lean 4 theorem from 0 (trivial/artificial) to 10 (landmark).",
            "criteria": DECISION_IMPORTANCE_LEVELS,
        },
        "msc_section": {
            "type": "choice",
            "instructions": "Choose the single best two-digit MSC 2020 subject area for this theorem.",
            "criteria": DECISION_MSC_CHOICES,
        },
        "surprising": {
            "type": "noul",
            "instructions": "Would a working mathematician find this theorem genuinely surprising (Novelty Level 4)?",
        },
        "human_cares": {
            "type": "noul",
            "instructions": "Would a human mathematician actually care about or cite this theorem (Novelty Level 5)?",
        },
    }

    answers = gemini_decisions(
        input_text=_candidate_summary_for_llm(meta),
        questions=questions,
        model=model,
        endpoint=decisions_endpoint,
    )

    kind_ans = answers.get("kind", {})
    kind = str(kind_ans.get("choice", "Proposition")).strip().capitalize()
    if kind not in VALID_KINDS:
        kind = "Proposition"
    kind_probs = kind_ans.get("probabilities", {})
    kind_p = float(kind_probs.get(kind, kind_ans.get("confidence", 0.5)))

    imp_ans = answers.get("importance", {})
    expected_score = float(imp_ans.get("score", 5.0))
    imp_conf = float(imp_ans.get("confidence", 0.5))
    importance = max(0, min(10, int(round(expected_score))))

    msc_ans = answers.get("msc_section", {})
    sec = str(msc_ans.get("choice", "")).strip()
    if sec not in MSC_SECTIONS:
        msc_code = _guess_msc_from_namespaces(meta.get("namespaces", []))
        sec = section_prefix(msc_code)
    else:
        msc_code = f"{sec}A05"

    p_surp = float(answers.get("surprising", {}).get("noul", 0.0))
    p_care = float(answers.get("human_cares", {}).get("noul", 0.0))

    justification = (
        f"Calibrated zero-token rubric evaluation assigns an expected importance of {expected_score:.2f}/10 "
        f"(confidence {imp_conf:.2f}) and classifies the result as a {kind} (p = {kind_p:.2f}) in MSC {sec}-XX. "
        f"Independent probability estimates yield P(surprising) = {p_surp:.2f} and "
        f"P(a human mathematician cares) = {p_care:.2f}."
    )

    return {
        "referee_id": referee_id,
        "model": model,
        "kind": kind,
        "importance": importance,
        "msc_code": msc_code,
        "justification": justification,
        "decision_metrics": {
            "expected_score": round(expected_score, 3),
            "score_confidence": round(imp_conf, 3),
            "kind_probability": round(kind_p, 3),
            "p_surprising": round(p_surp, 3),
            "p_human_cares": round(p_care, 3),
        },
    }


def run_decider(
    meta: dict[str, Any],
    *,
    referee_id: str,
    model: str,
    endpoint: str,
    persona_note: str,
    offline: bool = False,
    persona_bias: int = 0,
    decisions_endpoint: str = "https://generativelanguage.googleapis.com/v1beta/decisions",
) -> dict[str, Any]:
    if offline:
        return _offline_referee(meta, referee_id, persona_bias)

    if model.startswith("gemini-decision-"):
        return _run_decision_model_referee(
            meta,
            referee_id=referee_id,
            model=model,
            decisions_endpoint=decisions_endpoint,
        )

    sys_prompt = _load_prompt("decider") + f"\n\nReferee persona guidance: {persona_note}"
    user_prompt = _candidate_summary_for_llm(meta)

    raw = chat_completion(
        endpoint=endpoint,
        model=model,
        system_prompt=sys_prompt,
        user_prompt=user_prompt,
        temperature=0.85,
        max_tokens=400,
    )
    data = extract_json(raw)
    kind = str(data.get("kind", "Proposition")).strip().capitalize()
    if kind not in VALID_KINDS:
        kind = "Proposition"
    importance = max(0, min(10, int(round(float(data.get("importance", 5))))))
    msc_code = str(data.get("msc_code", "03B05")).strip().upper()
    if len(msc_code) < 2 or msc_code[:2] not in MSC_SECTIONS:
        msc_code = _guess_msc_from_namespaces(meta.get("namespaces", []))
    justification = str(data.get("justification", "")).strip()
    if not justification:
        justification = "The result is formally verified by the Lean kernel. Its broader mathematical significance remains to be determined."

    return {
        "referee_id": referee_id,
        "model": model,
        "kind": kind,
        "importance": importance,
        "msc_code": msc_code,
        "justification": justification,
    }


def _validate_press_release(text: str) -> bool:
    low = text.lower()
    has_first = re.search(r"\bfirst\b", low) is not None
    has_sota = ("state of the art" in low) or ("state-of-the-art" in low)
    return has_first and has_sota and len(text.split()) >= 20


def _format_proved_by(models: list[dict[str, Any]]) -> str:
    parts = [f"{m['family']}-{m['version']}-{m['tier']}" for m in models]
    return " & ".join(parts)


def render_editorial(editorial: dict[str, Any]) -> dict[str, Any]:
    """Derive the heading and announcement from the current result title."""
    previous_title, _, legacy_credit = editorial.get("eponym", "").partition(" | proved by ")
    title = editorial.get("title") or previous_title
    credit = editorial.get("proved_by") or legacy_credit
    eponym = f"{title} | proved by {credit}" if credit else title
    if body := editorial.get("press_release_body"):
        attribution = f", proved by {credit}" if credit else ""
        press = f"{ANNOUNCEMENT}{title}{attribution}. {body}"
    else:
        press = editorial.get("press_release", "")
        opening = press.removeprefix(ANNOUNCEMENT)
        _, separator, rest = opening.partition(", proved by ")
        if opening != press and separator:
            # Older offline records embedded the title directly in this opening.
            press = f"{ANNOUNCEMENT}{title}{separator}{rest}"
        elif previous_title and previous_title != title:
            press = press.replace(previous_title, title)
    return editorial | {"title": title, "eponym": eponym, "proved_by": credit, "press_release": press}


def _offline_math_title(meta: dict[str, Any], kind: str, joint_eponym: bool) -> str:
    """Synthesize a deadpan mathematical result title from the Lean statement & lemmas."""
    stmt = meta.get("statement_pretty", meta.get("statement_lean", ""))
    lemmas = _walk_lemmas(meta)
    joined = (stmt + " " + " ".join(lemmas)).lower()
    display_kind = "Inequality" if (joint_eponym and ("≤" in stmt or "<" in stmt)) else kind

    # Extract recognizable mathematical themes from the statement & Mathlib lemmas
    themes: list[tuple[str, str]] = [
        ("connectedcomponent", "Clopen Connected-Component Stability"),
        ("isclopen", "Finite Clopen Intersection"),
        ("addopposite", "Iterated Additive-Opposite Regularity"),
        ("isvaddregular", "Additive Regularity Transfer"),
        ("antitone", "Nested Min–Max Antitonicity"),
        ("monotone", "Composed Monotonicity"),
        ("order.succ", "Successor-Bound Supremum Absorption"),
        ("sup_of_le", "Lattice Supremum Absorption"),
        ("list_prod", "List-Product Square Commutation"),
        ("nonunitalnonassocring", "Non-Associative Ring Difference Commutation"),
        ("commute", "Ring Commutation Persistence"),
        ("string.slice", "String-Slice Offset Bound"),
        ("rawendpos", "Valid Slice-Position Bound"),
        ("hashmap", "HashMap Insertion Sublist"),
        ("injOn".lower(), "Restricted-Map Injectivity"),
        ("preimage", "Iterated Preimage Injectivity"),
        ("invfunon", "Powerset Image Inversion"),
        ("prime", "Primality Persistence"),
        ("coprime", "Coprimality Transfer"),
        ("subgroup", "Subgroup Closure"),
        ("ideal", "Ideal Absorption"),
        ("continuous", "Continuous Composition"),
        ("filter", "Filter Convergence"),
        ("finset", "Finite-Set Cardinality"),
    ]
    for needle, phrase in themes:
        if needle in joined:
            return f"The {phrase} {display_kind}"

    # Fallback: build a title from the last Mathlib lemma's stem + namespace
    ns = (meta.get("namespaces") or ["Formal"])[0]
    stem = lemmas[-1].split(".")[-1].replace("_", " ").title() if lemmas else "Forward Chain"
    return f"The {ns} {stem} {display_kind}"


def _offline_namer(
    meta: dict[str, Any],
    *,
    kind: str,
    joint_eponym: bool,
    families_state: dict[str, Any],
    blocklist: set[str],
    deprecate_after: int,
) -> dict[str, Any]:
    rng = random.Random(
        int(hashlib.sha256(f"namer:{meta['statement_hash']}".encode()).hexdigest()[:8], 16)
    )
    active = [
        (name, info)
        for name, info in families_state.get("families", {}).items()
        if not info.get("deprecated", False) and info.get("result_count", 0) < deprecate_after
    ]

    def pick_one(exclude: set[str]) -> tuple[str, str, str]:
        # 55% chance to reuse an active family so leaderboards accumulate meaningfully
        usable_active = [(n, i) for n, i in active if n not in exclude]
        if usable_active and rng.random() < 0.55:
            fam_name, info = rng.choice(usable_active)
            ver = format_version(info)
        else:
            candidates = [
                f
                for f in FALLBACK_FAMILIES
                if f not in exclude
                and not is_blocked_family(f, blocklist)
                and not families_state.get("families", {}).get(f, {}).get("deprecated", False)
            ]
            fam_name = rng.choice(candidates) if candidates else f"Zosterops{rng.randint(10,99)}"
            existing = families_state.get("families", {}).get(fam_name)
            ver = format_version(existing) if existing else f"{rng.randint(1, 5)}.{rng.randint(0, 4)}"
        tier = rng.choice(FALLBACK_TIERS)
        return fam_name, ver, tier

    f1, v1, t1 = pick_one(set())
    models = [{"family": f1, "version": v1, "tier": t1}]
    if joint_eponym:
        f2, v2, t2 = pick_one({f1})
        models.append({"family": f2, "version": v2, "tier": t2})

    press_body = (
        "This marks the first kernel-certified milestone of its tier in our ongoing frontier scaling "
        "evaluations. Achieving a new state of the art across our internal formal-verification "
        "benchmarks, the research program demonstrates unprecedented alignment between automated "
        "type-checked inference and post-human editorial standards."
    )
    return {
        "title": _offline_math_title(meta, kind, joint_eponym),
        "proved_by": _format_proved_by(models),
        "models": models,
        "press_release_body": press_body,
    }


def run_namer(
    meta: dict[str, Any],
    *,
    kind: str,
    joint_eponym: bool,
    families_state: dict[str, Any],
    blocklist: set[str],
    deprecate_after: int,
    model: str,
    endpoint: str,
    offline: bool = False,
) -> dict[str, Any]:
    if offline:
        return _offline_namer(
            meta,
            kind=kind,
            joint_eponym=joint_eponym,
            families_state=families_state,
            blocklist=blocklist,
            deprecate_after=deprecate_after,
        )

    sys_prompt = _load_prompt("namer")
    active_summary = {
        name: {"version": format_version(info), "count": info.get("result_count", 0)}
        for name, info in families_state.get("families", {}).items()
        if not info.get("deprecated", False)
    }
    retired = [
        name
        for name, info in families_state.get("families", {}).items()
        if info.get("deprecated", False)
    ]

    last_reason = ""
    for attempt in range(4):
        user_prompt = (
            f"Result kind: {kind}\n"
            f"Joint attribution required (both referees >= 8): {joint_eponym}\n"
            f"Active families you may reuse (use exact version shown) or invent a new one:\n"
            f"{json.dumps(active_summary, indent=2)}\n"
            f"Retired/legacy families (do NOT reuse): {retired}\n"
            f"Statement snippet (use to craft the mathematical title, but do NOT explain the math in the press release):\n"
            f"{_readable_statement(meta)[:400]}\n"
        )
        if last_reason:
            user_prompt += f"\nPrevious attempt rejected: {last_reason}. Please fix this.\n"

        raw = chat_completion(
            endpoint=endpoint,
            model=model,
            system_prompt=sys_prompt,
            user_prompt=user_prompt,
            temperature=0.95,
            max_tokens=500,
        )
        data = extract_json(raw)
        models = data.get("models", [])
        title = str(data.get("title", "")).strip()
        press_body = str(data.get("press_release_body", "")).strip()

        expected_n = 2 if joint_eponym else 1
        if not isinstance(models, list) or len(models) != expected_n:
            last_reason = f"Expected exactly {expected_n} model(s) in `models`"
            continue

        collision = False
        cleaned_models = []
        seen_fams: set[str] = set()
        for m in models:
            fam = re.sub(r"[^A-Za-z]", "", str(m.get("family", "")).strip())
            if fam:
                fam = fam[0].upper() + fam[1:]
            if is_blocked_family(fam, blocklist) or fam in retired or fam in seen_fams:
                last_reason = f"Family name '{fam}' is blocklisted, retired, or duplicated"
                collision = True
                break
            seen_fams.add(fam)
            # Enforce monotonically non-decreasing version if family exists
            existing = families_state.get("families", {}).get(fam)
            ver = format_version(existing) if existing else str(m.get("version", "1.0")).strip()
            tier = str(m.get("tier", "Ultra")).strip() or "Ultra"
            cleaned_models.append({"family": fam, "version": ver, "tier": tier})

        if collision:
            continue
        if not title:
            last_reason = "Missing mathematical `title` string"
            continue
        if not _validate_press_release(press_body):
            last_reason = "Press release body MUST include both 'first' and 'state of the art'"
            continue
        if title.casefold() in press_body.casefold():
            last_reason = "Press release body must omit the result title"
            continue

        return {
            "title": title,
            "proved_by": _format_proved_by(cleaned_models),
            "models": cleaned_models,
            "press_release_body": press_body,
        }

    # If LLM failed validation 4 times, fall back safely so pipeline never halts on a name collision
    return _offline_namer(
        meta,
        kind=kind,
        joint_eponym=joint_eponym,
        families_state=families_state,
        blocklist=blocklist,
        deprecate_after=deprecate_after,
    )


def run_gloss(
    meta: dict[str, Any],
    *,
    model: str,
    endpoint: str,
    offline: bool = False,
) -> str:
    if offline:
        lemmas = _walk_lemmas(meta)
        ns = ", ".join(meta.get("namespaces", [])[:4]) or "Mathlib"
        return (
            f"Informally, this statement chains {meta.get('steps_taken', 0)} verified forward inferences "
            f"drawn from {ns} (including {', '.join(lemmas[:3]) or 'standard library lemmas'}). "
            f"Given the surviving hypotheses after unused-variable pruning, the final conclusion holds "
            f"identically under Lean's standard classical axioms, though the hypotheses were assembled "
            f"mechanically rather than motivated by a human conjecture."
        )

    sys_prompt = _load_prompt("gloss")
    user_prompt = _candidate_summary_for_llm(meta)
    return chat_completion(
        endpoint=endpoint,
        model=model,
        system_prompt=sys_prompt,
        user_prompt=user_prompt,
        temperature=0.4,
        max_tokens=300,
    )


def scale_interest(score: float) -> float:
    """Map the generator's interest score onto the referees' 0 to 10 range."""
    return max(0.0, min(10.0, score / 4.0))


def screen_candidate(
    candidate: dict[str, Any],
    *,
    cfg: dict[str, Any],
    offline: bool = False,
) -> dict[str, Any]:
    """Score an unverified candidate with Referee A, for ranking a pool.

    Returns `{"score", "tie_break", "source", "verdict"}`. When the referee cannot be
    reached, the generator's own interest score ranks the candidate and `verdict` is None.
    """
    fallback = {
        "score": scale_interest(float(candidate.get("interest", {}).get("score", 0.0))),
        "tie_break": 0.0,
        "source": "interest_score",
        "verdict": None,
    }
    if offline or resolve_api_key() is None:
        return fallback
    llm_cfg = cfg["llm"]
    meta = candidate | {"interdisciplinarity": len(candidate.get("namespaces", []))}
    try:
        verdict = run_decider(
            meta,
            referee_id="Referee A",
            model=llm_cfg["decider_1_model"],
            endpoint=llm_cfg["endpoint"],
            decisions_endpoint=llm_cfg.get(
                "decisions_endpoint", "https://generativelanguage.googleapis.com/v1beta/decisions"
            ),
            persona_note=REFEREE_A_PERSONA,
            persona_bias=1,
        )
    except Exception as exc:  # noqa: BLE001 - a malformed reply must not sink a run after its walks
        print(f"  [screen] Referee A unavailable ({exc}); ranking by interest score.")
        return fallback
    metrics = verdict.get("decision_metrics", {})
    return {
        "score": float(metrics.get("expected_score", verdict["importance"])),
        "tie_break": float(metrics.get("p_human_cares", 0.0)),
        "source": "referee_a",
        "verdict": verdict,
    }


def register_families(
    models: list[dict[str, Any]],
    families_state: dict[str, Any],
    deprecate_after: int,
) -> list[dict[str, Any]]:
    """Update persistent family registry and return annotated model entries."""
    fams = families_state.setdefault("families", {})
    annotated = []
    for m in models:
        name = m["family"]
        if name not in fams:
            # Parse initial major.minor if numeric
            parts = re.findall(r"\d+", m.get("version", "1.0"))
            maj = int(parts[0]) if len(parts) >= 1 else 1
            mn = int(parts[1]) if len(parts) >= 2 else 0
            fams[name] = {
                "major": maj,
                "minor": mn,
                "result_count": 0,
                "deprecated": False,
            }
        entry = fams[name]
        entry["result_count"] = int(entry.get("result_count", 0)) + 1
        if entry["result_count"] >= deprecate_after:
            entry["deprecated"] = True
        annotated.append(
            {
                "family": name,
                "version": m["version"],
                "tier": m["tier"],
                "legacy": bool(entry["deprecated"]),
            }
        )
    return annotated


def process_editorial(
    meta: dict[str, Any],
    *,
    offline: bool = False,
    cfg: dict[str, Any] | None = None,
    families_state: dict[str, Any] | None = None,
    referee_a: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Run both referees, namer, and gloss for one verified candidate.

    A `referee_a` verdict obtained while screening is reused as Referee A's report,
    so the same result is never scored twice by the same referee.
    """
    cfg = cfg or load_config()
    llm_cfg = cfg["llm"]
    naming_cfg = cfg["naming"]
    endpoint = llm_cfg["endpoint"]
    decisions_endpoint = llm_cfg.get(
        "decisions_endpoint", "https://generativelanguage.googleapis.com/v1beta/decisions"
    )

    use_offline = offline or (resolve_api_key() is None)
    if not offline and use_offline:
        print("  [editorial] No LLM_API_KEY configured; using offline heuristic fallback.")

    if referee_a is not None:
        ref1 = referee_a
    else:
        try:
            ref1 = run_decider(
                meta,
                referee_id="Referee A",
                model=llm_cfg["decider_1_model"],
                endpoint=endpoint,
                decisions_endpoint=decisions_endpoint,
                persona_note=REFEREE_A_PERSONA,
                offline=use_offline,
                persona_bias=1,
            )
        except LLMError as exc:
            print(f"  [editorial] Referee A LLM failed ({exc}); falling back to offline heuristic.")
            ref1 = _offline_referee(meta, "Referee A", 1)

    try:
        ref2 = run_decider(
            meta,
            referee_id="Referee B",
            model=llm_cfg["decider_2_model"],
            endpoint=endpoint,
            decisions_endpoint=decisions_endpoint,
            persona_note=REFEREE_B_PERSONA,
            offline=use_offline,
            persona_bias=-1,
        )
    except LLMError as exc:
        # Fallback to decider_1_model, then offline heuristic if endpoint is unavailable
        print(f"  [editorial] Referee B model ({llm_cfg['decider_2_model']}) failed ({exc}); retrying on {llm_cfg['decider_1_model']}.")
        try:
            ref2 = run_decider(
                meta,
                referee_id="Referee B",
                model=llm_cfg["decider_1_model"],
                endpoint=endpoint,
                decisions_endpoint=decisions_endpoint,
                persona_note=REFEREE_B_PERSONA,
                offline=use_offline,
                persona_bias=-1,
            )
        except LLMError as exc2:
            print(f"  [editorial] Referee B fallback failed ({exc2}); using offline heuristic.")
            ref2 = _offline_referee(meta, "Referee B", -1)

    mean_imp = round((ref1["importance"] + ref2["importance"]) / 2.0, 1)
    # Use the higher-rated referee's classification & MSC (ties go to Referee A)
    primary = ref1 if ref1["importance"] >= ref2["importance"] else ref2
    kind = primary["kind"]
    msc_code = primary["msc_code"]
    msc_sec = section_prefix(msc_code)
    joint_threshold = int(naming_cfg.get("joint_eponym_min_score", 8))
    joint_eponym = (ref1["importance"] >= joint_threshold) and (ref2["importance"] >= joint_threshold)

    blocklist = load_blocklist()
    save_registry = families_state is None
    if families_state is None:
        families_state = load_families()
    deprecate_after = int(naming_cfg.get("deprecate_after", 50))

    try:
        named = run_namer(
            meta,
            kind=kind,
            joint_eponym=joint_eponym,
            families_state=families_state,
            blocklist=blocklist,
            deprecate_after=deprecate_after,
            model=llm_cfg["namer_model"],
            endpoint=endpoint,
            offline=use_offline,
        )
    except LLMError as exc:
        print(f"  [editorial] Namer LLM failed ({exc}); using offline fallback.")
        named = _offline_namer(
            meta,
            kind=kind,
            joint_eponym=joint_eponym,
            families_state=families_state,
            blocklist=blocklist,
            deprecate_after=deprecate_after,
        )
    annotated_families = register_families(named["models"], families_state, deprecate_after)
    if save_registry:
        save_families(families_state)

    try:
        gloss = run_gloss(
            meta,
            model=llm_cfg["gloss_model"],
            endpoint=endpoint,
            offline=use_offline,
        )
    except LLMError as exc:
        print(f"  [editorial] Gloss LLM failed ({exc}); using offline fallback.")
        gloss = run_gloss(meta, model=llm_cfg["gloss_model"], endpoint=endpoint, offline=True)

    return {
        "kind": kind,
        "mean_importance": mean_imp,
        "referee_disagreement": abs(ref1["importance"] - ref2["importance"]),
        "msc_code": msc_code,
        "msc_section": msc_sec,
        "msc_section_name": MSC_SECTIONS.get(msc_sec, "General"),
        "referees": [ref1, ref2],
        "title": named["title"],
        "proved_by": named["proved_by"],
        "joint_eponym": joint_eponym,
        "families": annotated_families,
        "press_release_body": named["press_release_body"],
        "unverified_gloss": gloss,
    }
