"""Zero-dependency OpenAI-compatible client targeting GitHub Models."""

from __future__ import annotations

import json
import os
import re
import subprocess
import time
import urllib.error
import urllib.request
from typing import Any


class LLMError(RuntimeError):
    """Raised when an LLM request fails or returns unparseable content."""


def resolve_api_key() -> str | None:
    """Resolve API key from LLM_API_KEY, GITHUB_TOKEN, or `gh auth token`."""
    for var in ("LLM_API_KEY", "GITHUB_TOKEN", "GH_TOKEN"):
        val = os.environ.get(var, "").strip()
        if val:
            return val
    try:
        out = subprocess.run(
            ["gh", "auth", "token"],
            check=True,
            capture_output=True,
            text=True,
            timeout=5,
        )
        tok = out.stdout.strip()
        if tok:
            return tok
    except Exception:
        pass
    return None


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
    """Call an OpenAI-compatible chat completions endpoint (e.g. GitHub Models)."""
    key = api_key or resolve_api_key()
    if not key:
        raise LLMError(
            "No API key found. Set LLM_API_KEY or GITHUB_TOKEN (with models: read), "
            "or authenticate with `gh auth login`."
        )

    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
        "temperature": temperature,
        "max_tokens": max_tokens,
    }
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
                raw = resp.read().decode("utf-8")
            data = json.loads(raw)
            content = data["choices"][0]["message"]["content"]
            if not isinstance(content, str) or not content.strip():
                raise LLMError(f"Empty response from model {model}")
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
    obj = json.loads(cleaned)
    if not isinstance(obj, dict):
        raise ValueError("Expected JSON object")
    return obj
