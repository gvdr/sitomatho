# AI dreams of Maths after too much cheese

> *Annals of Kernel-Checked Mathematics — Kernel-Checked Babel: a generator of verified, unimportant theorems.*

Deployed via GitHub Pages at **https://gvdr.github.io/sitomatho/** (`github.com/gvdr/sitomatho`).

A tongue-in-cheek web experiment and parody of automated mathematical discovery. Every theorem published here is genuinely type-checked by the **Lean 4** kernel against a pinned **Mathlib** release using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`), while every eponym, referee report, importance score, and press release is satire.

Identifiers follow our own non-academic scheme (`AKCM-2026-NNNN`), never DOIs or arXiv numbers.

## Architecture

- **`Babel/`** — Lean 4 metaprogram (`lake exe walk`):
  - **Generator A**: random forward walk over Mathlib's theorem environment, biased toward crossing namespaces, with unused-hypothesis shrinking and clean standalone `.lean` emission.
  - **Novelty Gate & Badges (Levels 0–3)**: alpha-invariant expression hashing (L0), `exact?` lookup gate (L1), `simp` / `aesop` routine checks (L2), and post-shrinking proof-to-statement AST depth ratio (L3).
- **`scripts/`** — Python orchestration, verification, editorial desk, and static site generator:
  - `scripts/verify.py`: runs `lake env lean` + `#print axioms` on standalone `results/*/Result.lean` files.
  - `scripts/editorial.py`: runs two independent LLM referees (via GitHub Models with `GITHUB_TOKEN`, or any OpenAI-compatible endpoint via `LLM_ENDPOINT` + `LLM_API_KEY`), the blocklisted AI-model Namer (monotonically increasing versions per issue, deprecation at 50 results, joint eponyms when both referees rate ≥ 8, press releases requiring `"first"` and `"state of the art"`), and the Unverified Gloss.
  - `scripts/pipeline.py`: ties together `walk` → kernel verification → editorial desk → issue publication.
  - `scripts/build_site.py`: Jinja2 static journal generator producing `_site/` (Issues grouped by MSC 2020, Result pages with inline SVG Mathlib dependency graphs, Leaderboard, Retractions, About, and per-issue + site-wide Atom feeds).
- **`results/AKCM-YYYY-NNNN/`** — Git as the database (`Result.lean` + `meta.json`).
- **`.github/workflows/`**:
  - `pages.yml`: verifies all Lean results and deploys `_site/` to GitHub Pages.
  - `nightly.yml`: nightly theorem generation & editorial labeling (using `GITHUB_TOKEN` with `models: read`) and weekly issue publication.

## Local usage

```bash
# 1. Restore prebuilt Mathlib cache & build Generator A
lake exe cache get
lake build Babel walk

# 2. Generate, kernel-verify, referee, name, and publish an issue
#    (uses GITHUB_TOKEN / LLM_API_KEY / `gh auth token` for GitHub Models, or pass --offline)
.venv/bin/python scripts/pipeline.py --seed 20261124 --count 10 --publish-issue

# 3. Verify all standalone Result.lean files and axioms
.venv/bin/python scripts/verify.py

# 4. Build the static journal site into _site/
SITE_BASE_PATH="" .venv/bin/python scripts/build_site.py
python3 -m http.server -d _site 8000
```

## Configuration

Edit [`akcm.toml`](akcm.toml) to set your repository slug (`base_url`, `base_path`, `repo_url`) and default GitHub Models identifiers. In GitHub Actions, `pages.yml` automatically derives the GitHub Pages base URL and path from `GITHUB_REPOSITORY`.
