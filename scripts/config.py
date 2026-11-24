"""Configuration loader for Annals of Kernel-Checked Mathematics."""

from __future__ import annotations

import os
import tomllib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent


def load_config() -> dict[str, Any]:
    cfg_path = ROOT / "akcm.toml"
    with cfg_path.open("rb") as f:
        cfg = tomllib.load(f)

    # Auto-derive GitHub Pages URLs in GitHub Actions if GITHUB_REPOSITORY is set
    gh_repo = os.environ.get("GITHUB_REPOSITORY")
    if gh_repo and "/" in gh_repo:
        owner, repo = gh_repo.split("/", 1)
        cfg["site"]["repo_url"] = f"https://github.com/{owner}/{repo}"
        if repo.lower() == f"{owner.lower()}.github.io":
            cfg["site"]["base_url"] = f"https://{owner}.github.io"
            cfg["site"]["base_path"] = ""
        else:
            cfg["site"]["base_url"] = f"https://{owner}.github.io/{repo}"
            cfg["site"]["base_path"] = f"/{repo}"

    if env_base := os.environ.get("SITE_BASE_URL"):
        cfg["site"]["base_url"] = env_base.rstrip("/")
    if (env_path := os.environ.get("SITE_BASE_PATH")) is not None:
        cfg["site"]["base_path"] = env_path.rstrip("/")
    if env_repo := os.environ.get("SITE_REPO_URL"):
        cfg["site"]["repo_url"] = env_repo.rstrip("/")

    if env_ep := os.environ.get("LLM_ENDPOINT"):
        cfg["llm"]["endpoint"] = env_ep
    if env_m1 := os.environ.get("DECIDER_1_MODEL"):
        cfg["llm"]["decider_1_model"] = env_m1
    if env_m2 := os.environ.get("DECIDER_2_MODEL"):
        cfg["llm"]["decider_2_model"] = env_m2
    if env_mn := os.environ.get("NAMER_MODEL"):
        cfg["llm"]["namer_model"] = env_mn
    if env_mg := os.environ.get("GLOSS_MODEL"):
        cfg["llm"]["gloss_model"] = env_mg

    return cfg
