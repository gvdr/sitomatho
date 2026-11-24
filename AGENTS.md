# Repository Guidelines

## Project Structure and Module Organization

- `Babel/` contains the Lean 4 theorem generator, novelty checks, proof transformations, and the `walk` executable. Lake pins Lean and Mathlib via `lean-toolchain` and `lakefile.toml`.
- `scripts/` contains the Python pipeline, editorial logic, Lean verifier, site builder, and tests in `scripts/test_akcm.py`. Editorial prompts live in `prompts/`.
- `results/AKCM-YYYY-NNNN/` pairs each standalone `Result.lean` with its `meta.json`. `state/` tracks issues, model families, the blocklist, and retractions.
- `site/templates/` and `site/static/` hold the Jinja2 templates and static assets. GitHub Actions handles scheduled generation and Pages deployment.

## Build, Test, and Development Commands

Run these from the repository root with Lake on your PATH and Python 3.12, as used in CI.

- `lake exe cache get` fetches prebuilt Mathlib artifacts. `lake build Babel Corpus walk` builds the Lean targets.
- `python -m pip install -r requirements.txt` installs Jinja2 in your active Python environment.
- `python scripts/pipeline.py --seed 20261124 --count 1 --offline` exercises generation and editorial processing without model credentials. Accepted results update `results/` and may update `state/`.
- `SITE_BASE_PATH="" python scripts/build_site.py` generates `_site/`. Preview it with `python -m http.server -d _site 8000`.

## Coding Style and Naming Conventions

Use two-space indentation and camelCase helpers in Lean, and four-space indentation and snake_case functions in Python. Keep Lean binders explicit because `autoImplicit` is disabled. Match result IDs such as `AKCM-2026-0001` to Lean theorem names such as `akcm_2026_0001`.

## Testing Guidelines

Run `python scripts/test_akcm.py` for the assertion-based Python suite and `lake build BabelTest` for the Lean checks in `Babel/Tests.lean`, where a failing `#guard` fails the build. Name cases `test_*` and register them in the script’s main block. Run `python scripts/verify.py` to check every result against the Lean kernel and axiom allowlist, as Pages CI does. Pass a result directory to verify just that result. After changing the generator, run `python scripts/bench_walk.py --label <name> --strict` to check yield, timing, and the non-triviality invariants on the fixed benchmark modules.

## Commit and Pull Request Guidelines

Use short, descriptive commit subjects. Follow the imperative style of the recent configuration commit, for example `Update the issue feed`. In pull requests, describe what changed, link any related issue, and list the checks you ran. For visual changes, include a screenshot of the affected page.
