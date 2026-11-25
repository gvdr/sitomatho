"""Zero-dependency OpenAI-compatible HTTP client for AKCM editorial models."""

from __future__ import annotations

import json
import os
import re
import time
import urllib.error
import urllib.request
from typing import Any


class LLMError(RuntimeError):
    """Raised when an LLM request fails or returns unparseable content."""


def resolve_api_key() -> str | None:
    """Resolve API key from LLM_API_KEY or common provider env vars."""
    for var in (
        "LLM_API_KEY",
        "OPENROUTER_API_KEY",
        "GEMINI_API_KEY",
        "OPENAI_API_KEY",
        "GROQ_API_KEY",
    ):
        val = os.environ.get(var, "").strip()
        if val:
            return val
    return None


def normalize_endpoint(endpoint: str) -> str:
    """Allow passing either a base URL (.../openai/) or full .../chat/completions URL."""
    ep = endpoint.strip().rstrip("/")
    if not ep.endswith("/chat/completions"):
        ep = ep + "/chat/completions"
    return ep


def chat_completion(
    *,
    endpoint: str,
    model: str,
    system_prompt: str,
    user_prompt: str,
    api_key: str | None = None,
    temperature: float = 0.8,
    max_tokens: int = 700,
    retries: int = 3,
    timeout: int = 60,
) -> str:
    """Call an OpenAI-compatible chat completions endpoint."""
    endpoint = normalize_endpoint(endpoint)
    key = api_key or resolve_api_key()
    if not key:
        raise LLMError(
            "No API key found. Set LLM_API_KEY (or OPENROUTER_API_KEY / GEMINI_API_KEY / "
            "OPENAI_API_KEY / GROQ_API_KEY)."
        )

    payload: dict[str, Any] = {
        "model": model,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
        "temperature": temperature,
        "max_tokens": max(max_tokens, 2048) if model.startswith("gemini-") else max_tokens,
    }
    if model.startswith("gemini-4-"):
        payload["reasoning_effort"] = "low"
    body = json.dumps(payload).encode("utf-8")

    last_err: Exception | None = None
    for attempt in range(retries):
        req = urllib.request.Request(
            endpoint,
            data=body,
            method="POST",
            headers={
                "Content-Type": "application/json",
                "Accept": "application/json",
                "Authorization": f"Bearer {key}",
                "User-Agent": "AKCM-Editorial-Desk/1.0",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                status = getattr(resp, "status", 200)
                ctype = resp.headers.get("Content-Type", "")
                raw = resp.read().decode("utf-8", errors="replace")
            try:
                data = json.loads(raw)
            except json.JSONDecodeError as exc:
                raise LLMError(
                    f"Non-JSON response (HTTP {status}, {ctype}) from {endpoint}: {raw[:200]!r}"
                ) from exc
            choice = data["choices"][0]
            msg = choice.get("message") or {}
            content = msg.get("content")
            if not isinstance(content, str) or not content.strip():
                finish = choice.get("finish_reason", "unknown")
                raise LLMError(
                    f"Empty content from model {model} (finish_reason={finish}, keys={sorted(msg.keys())})"
                )
            return content.strip()
        except urllib.error.HTTPError as exc:
            err_body = exc.read().decode("utf-8", errors="replace")
            last_err = LLMError(f"HTTP {exc.code} from {model}: {err_body[:400]}")
            if exc.code in (429, 500, 502, 503, 504) and attempt + 1 < retries:
                time.sleep(2.0 * (attempt + 1))
                continue
            raise last_err from exc
        except Exception as exc:
            last_err = exc
            if attempt + 1 < retries:
                time.sleep(1.5 * (attempt + 1))
                continue
            raise LLMError(f"Request to {model} failed: {exc}") from exc

    raise LLMError(f"Exhausted retries for {model}: {last_err}")


def gemini_decisions(
    *,
    input_text: str,
    questions: dict[str, Any],
    model: str = "gemini-decision-1",
    endpoint: str = "https://generativelanguage.googleapis.com/v1beta/decisions",
    api_key: str | None = None,
    retries: int = 3,
    timeout: int = 60,
) -> dict[str, Any]:
    """Call the Gemini Decisions API (zero-output-token noul/choice/score evaluation)."""
    key = api_key or resolve_api_key()
    if not key:
        raise LLMError(
            "No API key found for Gemini Decisions API. Set LLM_API_KEY or GEMINI_API_KEY."
        )

    payload = {
        "model": model,
        "input": input_text,
        "questions": questions,
    }
    body = json.dumps(payload).encode("utf-8")

    last_err: Exception | None = None
    for attempt in range(retries):
        req = urllib.request.Request(
            endpoint.strip(),
            data=body,
            method="POST",
            headers={
                "Content-Type": "application/json",
                "Accept": "application/json",
                "x-goog-api-key": key,
                "User-Agent": "AKCM-Editorial-Desk/1.0",
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                status = getattr(resp, "status", 200)
                ctype = resp.headers.get("Content-Type", "")
                raw = resp.read().decode("utf-8", errors="replace")
            try:
                data = json.loads(raw)
            except json.JSONDecodeError as exc:
                raise LLMError(
                    f"Non-JSON response (HTTP {status}, {ctype}) from {endpoint}: {raw[:200]!r}"
                ) from exc
            answers = data.get("answers")
            if not isinstance(answers, dict):
                raise LLMError(f"Unexpected Decisions API payload from {model}: {raw[:300]}")
            return answers
        except urllib.error.HTTPError as exc:
            err_body = exc.read().decode("utf-8", errors="replace")
            last_err = LLMError(f"HTTP {exc.code} from {model}: {err_body[:400]}")
            if exc.code in (429, 500, 502, 503, 504) and attempt + 1 < retries:
                time.sleep(2.0 * (attempt + 1))
                continue
            raise last_err from exc
        except Exception as exc:
            last_err = exc
            if attempt + 1 < retries:
                time.sleep(1.5 * (attempt + 1))
                continue
            raise LLMError(f"Decisions request to {model} failed: {exc}") from exc

    raise LLMError(f"Exhausted retries for {model}: {last_err}")


def extract_json(text: str) -> dict[str, Any]:
    """Extract the first JSON object from an LLM reply (tolerating code fences)."""
    cleaned = text.strip()
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", cleaned, flags=re.DOTALL)
    if fence:
        cleaned = fence.group(1)
    else:
        start = cleaned.find("{")
        end = cleaned.rfind("}")
        if start != -1 and end != -1 and end > start:
            cleaned = cleaned[start : end + 1]
    try:
        obj = json.loads(cleaned)
    except json.JSONDecodeError as exc:
        raise LLMError(f"Reply is not valid JSON ({exc})") from exc
    if not isinstance(obj, dict):
        raise LLMError("Reply is not a JSON object")
    return obj
