# Interesting Theorems Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the specialist search produce unpadded, concept-crossing theorems, let the referee choose what is published, and make the generator measurable and faster.

**Architecture:** The Lean walk gains statistics, step-level triviality checks, and a search that keeps its best-scoring derivations as closed terms and runs the expensive gates only on those. The Python pipeline runs walks in parallel, reads output that survives a timeout, screens a candidate pool with Referee A, and verifies down the ranking. Module choice is steered by past screening scores.

**Tech Stack:** Lean 4 `v4.36.0` with Mathlib `v4.36.0` (MetaM, `Simp`, `Aesop`, `DiscrTree`), Lake, Python 3.12 standard library, Jinja2 (untouched).

**Spec:** `docs/superpowers/specs/2026-11-25-interesting-theorems-design.md`

## Global Constraints

- Lean and Mathlib stay pinned at `v4.36.0`. No new Lake or pip dependencies.
- Everything must run with `--offline` and with no API key. No task may require a live referee call to pass its tests.
- Do not edit `prompts/decider.md`, `DECISION_IMPORTANCE_LEVELS`, the decision questions, or `_offline_referee` in `scripts/editorial.py`.
- `scripts/verify.py` and the axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`) are unchanged.
- All randomness in Lean goes through the threaded `Babel.Rng`. Checks inside Lean are bounded by heartbeats. Wall-clock time is recorded for statistics and never influences a decision.
- `meta.json` changes are additive. Existing results must still render with `scripts/build_site.py`.
- Python tests are plain `test_*` functions in `scripts/test_akcm.py`, each also called in its `__main__` block. Run with `.venv/bin/python scripts/test_akcm.py`.
- Lean tests live in `Babel/Tests.lean` and run with `~/.elan/bin/lake build BabelTest`. A failing `#guard` or `#guard_msgs` fails the build.
- Lean: two-space indentation, camelCase, explicit binders. Python: four-space indentation, snake_case. Commit subjects are short and imperative.
- Prose in docs: no em-dashes, no "not A but B" contrasts.
- Work on branch `interesting-theorems`, not `main`.
- One walk process peaks near 1.5 GB of memory; the nightly job has 90 minutes.

## Review Focus

1. A conclusion that is itself a `∀` or an implication (for example `Antitone f`-style statements written out, or `∀ x ∈ l, …`). Reopening a closed statement must open exactly the recorded number of binders, otherwise hypotheses and conclusion are split in the wrong place. Test in Task 8.
2. A walk killed before it writes anything, or a missing output file. `read_walk_output` must return an empty, incomplete run and the pipeline must continue with the other profiles. Test in Task 2.
3. A pool smaller than the requested count, including an empty pool. Wander publishes what verified and exits 0; launch writes nothing and exits 1. Test in Task 12.
4. Screening that succeeds for some candidates and fails for others in one pool, and candidates with no `interest` field. Ranking must stay total and each record must show its ranking source. Tests in Tasks 10 and 11.
5. `state/wander.json` entries written before this change (no score fields) and a missing `state/candidates.jsonl`. Module selection and log appending must work. Tests in Tasks 11 and 12.

## File Structure

| File | Responsibility |
|---|---|
| `Babel/Stats.lean` (new) | Rejection reasons, counters, phase timers, JSON encoding |
| `Babel/Interest.lean` (new) | Concept extraction, interest components and score, padded-fact check, step limits |
| `Babel/Tests.lean` (new) | `#guard` and `#guard_msgs` checks for the two modules above and for closed-term rendering |
| `Babel/Gate.lean` | Gates with a real simp set, per-gate timing, hard Level 2 option |
| `Babel/Generator.lean` | Step checks in `tryApplyLemma`, closed kept derivations, best-of-walk specialist loop, gate order |
| `Babel/Walk.lean` | New flags, incremental output file, statistics in output |
| `scripts/walk_runner.py` (new) | `WalkRun`, `read_walk_output`, `run_walk`, `run_walks_parallel` (moved out of `pipeline.py`) |
| `scripts/bench_walk.py` (new) | Fixed benchmark, invariant checker, summary file |
| `scripts/selection.py` (new) | Pool entries, ranking, verify-down-the-ranking, candidate log |
| `scripts/editorial.py` | `screen_candidate`, `scale_interest`, precomputed Referee A |
| `scripts/wander.py` | New profile knobs, score fields in history, score-weighted drift |
| `scripts/pipeline.py` | Orchestration of the above in `run_wander`, `run_launch`, `main` |
| `docs/superpowers/specs/bench/` (new) | Benchmark summaries: `baseline.json`, `part1.json`, `part2.json`, `final.json` |

---

## Part 1: measurement and plumbing

### Task 1: Statistics module and Lean test target

**Files:**
- Create: `Babel/Stats.lean`, `Babel/Tests.lean`
- Modify: `lakefile.toml`, `Babel.lean`

**Interfaces:**
- Produces:
  ```lean
  namespace Babel
  inductive Reject
    | selfReuse | repeatedLemma | paddedFact | sizeCap | noUnifier | heartbeat
    | fewSteps | fewConcepts | noFocusSymbol | kernelCheck | badAxioms
    | closedByExact | closedBySimp | closedByAesop | unrenderable | duplicateHash
  def Reject.key : Reject → String          -- snake_case, e.g. "self_reuse", "closed_by_exact"
  structure WalkStats where
    phaseMs : Std.HashMap String Nat := {}
    rejects : Std.HashMap String Nat := {}
    attempts : Nat := 0
    applicationsTried : Nat := 0
    applicationsSucceeded : Nat := 0
  def WalkStats.bump (s : WalkStats) (r : Reject) : WalkStats
  def WalkStats.addMs (s : WalkStats) (phase : String) (ms : Nat) : WalkStats
  def WalkStats.dominantReject (s : WalkStats) : Option (String × Nat)   -- highest count, ties by key order
  def WalkStats.toJson (s : WalkStats) : Lean.Json
  abbrev StatsRef := IO.Ref WalkStats
  def StatsRef.reject (ref : StatsRef) (r : Reject) : BaseIO Unit
  def timed {α : Type} (ref : StatsRef) (phase : String) (act : MetaM α) : MetaM α   -- IO.monoMsNow, adds even when act throws
  ```
  Phase keys used everywhere: `import`, `index`, `hyp_tree`, `search`, `gate_exact`, `gate_simp`, `gate_aesop`, `render`.
  `toJson` shape: `{"phase_ms": {...}, "rejects": {...}, "attempts": n, "applications_tried": n, "applications_succeeded": n, "dominant_reject": "key" | null}`.

- [ ] **Step 1: Add the test library.** In `lakefile.toml` add `[[lean_lib]] name = "BabelTest"` with `roots = ["Babel.Tests"]`. Leave `defaultTargets` unchanged.

- [ ] **Step 2: Write failing checks in `Babel/Tests.lean`.**

```lean
import Babel.Stats
open Babel

#guard (({} : WalkStats).bump .selfReuse |>.bump .selfReuse).rejects.getD "self_reuse" 0 == 2
#guard (({} : WalkStats).addMs "search" 40 |>.addMs "search" 2).phaseMs.getD "search" 0 == 42
#guard (({} : WalkStats).bump .closedByExact |>.bump .paddedFact |>.bump .paddedFact).dominantReject
  == some ("padded_fact", 2)
#guard ({} : WalkStats).dominantReject == none
```

- [ ] **Step 3: Run** `~/.elan/bin/lake build BabelTest`. Expected: fails, `Babel.Stats` not found.

- [ ] **Step 4: Implement `Babel/Stats.lean`** with the interface above and add `import Babel.Stats` to `Babel.lean`.

- [ ] **Step 5: Run** `~/.elan/bin/lake build Babel BabelTest`. Expected: builds with no errors.

- [ ] **Step 6: Commit** `Add walk statistics module and Lean test target`.

### Task 2: Output file that survives a timeout

**Files:**
- Modify: `Babel/Walk.lean`, `scripts/pipeline.py`, `scripts/test_akcm.py`
- Create: `scripts/walk_runner.py`

**Interfaces:**
- Consumes: `WalkStats.toJson`, `timed`, `StatsRef` from Task 1.
- Produces (Lean): output file is one JSON object `{"complete": bool, "stats": {...}, "candidates": [...]}`. `writeOutput (path : System.FilePath) (complete : Bool) (stats : WalkStats) (cands : Array WalkCandidate) : IO Unit` writes `<path>.tmp` then renames it over `<path>`. It is called before the search starts (empty list, `complete = false`), after every accepted candidate, and at exit with `complete = true`.
- Produces (Python, `scripts/walk_runner.py`):
  ```python
  @dataclass
  class WalkRun:
      candidates: list[dict[str, Any]] = field(default_factory=list)
      stats: dict[str, Any] = field(default_factory=dict)
      complete: bool = False
      timed_out: bool = False

  def read_walk_output(path: Path) -> WalkRun      # missing or unparsable file -> WalkRun()
  def run_walk(*, seed, count, min_steps, max_steps, max_attempts, interdisciplinary,
               exact_heartbeats, aesop_heartbeats, convolute, module=None, focus=None,
               min_proof_depth=8, trials_per_walk=240, timeout=240) -> WalkRun
  ```
  `run_walk` moves here from `pipeline.py` unchanged in behaviour except: on `subprocess.TimeoutExpired` it returns `read_walk_output(out_file)` with `timed_out=True` and raises nothing; on a non-zero exit it still raises `RuntimeError`. `pipeline.py` imports `run_walk` and `WalkRun` from this module so `patch("pipeline.run_walk")` keeps working.

- [ ] **Step 1: Write failing tests** in `scripts/test_akcm.py`:

```python
def test_read_walk_output_partial_and_missing() -> None:
    with TemporaryDirectory() as directory:
        path = Path(directory) / "walk.json"
        assert read_walk_output(path) == WalkRun()
        path.write_text("{not json", encoding="utf-8")
        assert read_walk_output(path) == WalkRun()
        path.write_text(json.dumps({"complete": False, "stats": {"attempts": 3},
                                    "candidates": [{"statement_hash": "a"}]}), encoding="utf-8")
        run = read_walk_output(path)
        assert run.candidates == [{"statement_hash": "a"}] and not run.complete
        assert run.stats["attempts"] == 3

def test_run_walk_timeout_keeps_partial_output() -> None:
    # patch walk_runner.ROOT to a temp dir, walk_runner.find_lake to "lake", and
    # walk_runner.subprocess.run with a side effect that writes one candidate to the
    # --out path taken from the command, then raises subprocess.TimeoutExpired.
    run = run_walk(seed=7, count=2, min_steps=3, max_steps=8, max_attempts=5,
                   interdisciplinary=2.0, exact_heartbeats=1, aesop_heartbeats=1,
                   convolute=0, timeout=1)
    assert run.timed_out and len(run.candidates) == 1
```

- [ ] **Step 2: Run** `.venv/bin/python scripts/test_akcm.py`. Expected: `ImportError` for `walk_runner`.

- [ ] **Step 3: Implement `scripts/walk_runner.py`** and update `pipeline.py` callers to use `run.candidates`. In `test_launch_replaces_issue_only_after_full_verification`, wrap each mocked list as `WalkRun(candidates=[...], complete=True)`.

- [ ] **Step 4: Implement `writeOutput` in `Babel/Walk.lean`** and wrap the phases `import`, `index`, `hyp_tree`, `search` with `timed`. Set `stats.attempts`. Print a one-line summary of phase times and the dominant rejection to stderr at exit.

- [ ] **Step 5: Run** `.venv/bin/python scripts/test_akcm.py` and `~/.elan/bin/lake build Babel Corpus walk`, then
  `.venv/bin/python scripts/pipeline.py --seed 20261124 --count 1 --offline` followed by `git status --short results state`.
  Expected: tests pass; the pipeline run completes; revert any files it wrote under `results/` and `state/` with `git checkout -- results state` and delete new result directories.

- [ ] **Step 6: Commit** `Write walk output incrementally and keep partial results on timeout`.

### Task 3: Rejection counters and gate timing

**Files:**
- Modify: `Babel/Gate.lean`, `Babel/Generator.lean`, `Babel/Walk.lean`

**Interfaces:**
- Consumes: `StatsRef`, `Reject`, `timed` from Task 1.
- Produces: `tryApplyLemma`, `finishWalk`, `runWalkLoop`, `runSpecialistLoop`, `runSingleWalk` and `evaluateNovelty` each take a `stats : StatsRef` argument. Behaviour is otherwise unchanged in this task, so that Task 4 records a true baseline.
  - `tryApplyLemma` increments `applicationsTried` on entry, `applicationsSucceeded` when `mkStep` returns a step, and records `noUnifier` when no explicit binder matches.
  - `finishWalk` records one of `fewSteps`, `noFocusSymbol`, `kernelCheck`, `badAxioms`, `closedByExact`, `unrenderable` at each early return.
  - `evaluateNovelty` wraps its three checks in `timed` with `gate_exact`, `gate_simp`, `gate_aesop`; `finishWalk` wraps rendering in `timed … "render"`.
  - `tryCatchRuntimeEx` handlers in the specialist loop record `heartbeat`.

- [ ] **Step 1: Thread the argument and add the counters.** No new test file: the check is the run in Step 2.

- [ ] **Step 2: Run** `~/.elan/bin/lake build Babel Corpus walk` and then

```bash
~/.elan/bin/lake exe walk --seed 4242 --count 2 --max-steps 12 --max-attempts 20 \
  --module Mathlib.Order.Filter.Basic --focus Mathlib.Order.Filter \
  --min-proof-depth 6 --trials-per-walk 180 --convolute 0 --out .tmp/t3.json
.venv/bin/python -c "import json; s=json.load(open('.tmp/t3.json'))['stats']; print(s); assert s['applications_tried'] > 0 and 'gate_exact' in s['phase_ms']"
```
Expected: the assertion passes and the printed statistics contain non-zero `search` time.

- [ ] **Step 3: Commit** `Count rejections and time the gates in the walk`.

### Task 4: Benchmark, invariant checker, baseline

**Files:**
- Create: `scripts/bench_walk.py`, `docs/superpowers/specs/bench/baseline.json`
- Modify: `scripts/test_akcm.py`

**Interfaces:**
- Consumes: `run_walk`, `WalkRun` from Task 2.
- Produces:
  ```python
  BENCH_SEEDS = (20261124, 20261125)
  BENCH_ARGS = dict(count=4, min_steps=3, max_steps=12, max_attempts=40, interdisciplinary=2.5,
                    exact_heartbeats=150000, aesop_heartbeats=150000, convolute=0,
                    min_proof_depth=6, trials_per_walk=180, timeout=300)

  def check_invariants(candidate: dict, *, max_lemma_repeats: int = 1,
                       max_statement_size: int | None = None,
                       min_concepts: int | None = None) -> list[str]
  ```
  `check_invariants` returns violation strings. It reports `"lemma_repeated:<name>"` when a lemma occurs more than `max_lemma_repeats` times in `dependencies.nodes`; `"padded"` when `checks.simp_normal` is present and false; `"premise_reuse"` when `checks.premise_reuse` is present and non-zero; `"too_large"` and `"few_concepts"` when the optional bounds are given and `interest.statement_size` or `interest.concepts` violate them. Missing `checks` or `interest` produce no violation for those keys (the baseline has neither).
  The script runs `pipeline.LAUNCH_PROFILES × BENCH_SEEDS` sequentially, and writes `docs/superpowers/specs/bench/<label>.json` containing, per run: module, seed, wall seconds, candidate count, `timed_out`, `stats`, and violations per candidate; plus totals: `wall_seconds`, `candidates`, `valid_candidates` (candidates with no violation), `modules_with_valid` (count of modules with at least one), `seconds_per_valid_candidate` (`null` when there is none), `violations`. Flags: `--label` (required), `--strict` (exit 1 on any violation), `--min-concepts`, `--max-statement-size`.

- [ ] **Step 1: Write the failing test.**

```python
def test_bench_invariants() -> None:
    node = lambda name: {"id": name, "lemma": name, "kind": "mathlib"}
    padded = {"dependencies": {"nodes": [node("A.u"), node("A.i"), node("A.u")]},
              "checks": {"simp_normal": False, "premise_reuse": 2},
              "interest": {"statement_size": 900, "concepts": 1}}
    assert check_invariants(padded, max_statement_size=400, min_concepts=3) == [
        "lemma_repeated:A.u", "padded", "premise_reuse", "too_large", "few_concepts"]
    clean = {"dependencies": {"nodes": [node("A.u"), node("B.v")]},
             "checks": {"simp_normal": True, "premise_reuse": 0},
             "interest": {"statement_size": 120, "concepts": 3}}
    assert check_invariants(clean, max_statement_size=400, min_concepts=3) == []
    assert check_invariants({"dependencies": {"nodes": [node("A.u")]}}) == []
```

- [ ] **Step 2: Run** the test suite. Expected: `ImportError` for `bench_walk`.

- [ ] **Step 3: Implement `scripts/bench_walk.py`.**

- [ ] **Step 4: Run** the test suite (expected: pass), then record the baseline:
  `.venv/bin/python scripts/bench_walk.py --label baseline`. This takes up to 40 minutes; run it in the background. Expected: `baseline.json` exists and its totals show at least one `lemma_repeated` violation.

- [ ] **Step 5: Commit** `Add walk benchmark and record the baseline`.

### Task 5: Parallel walks and cheap-before-expensive gate order

**Files:**
- Modify: `scripts/walk_runner.py`, `scripts/pipeline.py`, `scripts/test_akcm.py`, `Babel/Generator.lean`
- Create: `docs/superpowers/specs/bench/part1.json`

**Interfaces:**
- Produces:
  ```python
  def run_walks_parallel(jobs: list[Callable[[], WalkRun]], *, workers: int) -> list[WalkRun]
  ```
  Results are returned in the order of `jobs`. A job that raises yields `WalkRun()` and a printed message. `pipeline.py` gains `--workers` (default `max(1, (os.cpu_count() or 2) // 2)`), passed to `run_wander` and `run_launch`. Both functions first run all profile walks through `run_walks_parallel` (each job being the existing per-profile walk, retry included), then consume the runs in profile order with the existing acceptance logic.
- In `finishWalk`, move the duplicate-statement check and `renderStandaloneLean` ahead of `evaluateNovelty`. `finishWalk` gains `seen : Std.HashSet String` and records `duplicateHash`.

- [ ] **Step 1: Write the failing tests.**

```python
def test_parallel_walks_preserve_order_and_isolate_failures() -> None:
    def job(tag: str, delay: float, fail: bool = False):
        def run() -> WalkRun:
            time.sleep(delay)
            if fail:
                raise RuntimeError("boom")
            return WalkRun(candidates=[{"statement_hash": tag}], complete=True)
        return run
    runs = run_walks_parallel([job("a", 0.2), job("b", 0.0, fail=True), job("c", 0.05)], workers=3)
    assert [[c["statement_hash"] for c in r.candidates] for r in runs] == [["a"], [], ["c"]]
```

- [ ] **Step 2: Run** the suite. Expected: `ImportError` for `run_walks_parallel`.

- [ ] **Step 3: Implement** `run_walks_parallel` with `concurrent.futures.ThreadPoolExecutor`, restructure `run_wander` and `run_launch`, add `--workers`.

- [ ] **Step 4: Reorder `finishWalk`** as described.

- [ ] **Step 5: Run** the suite and `~/.elan/bin/lake build Babel Corpus walk`, then `.venv/bin/python scripts/bench_walk.py --label part1`. Expected: tests pass; `part1.json` total wall seconds is at most the baseline's and candidate counts per run are equal to the baseline's.

- [ ] **Step 6: Conditional fix.** If in `part1.json` the `hyp_tree` phase exceeds 30% of wall time for any run, lower `ambientCap` in `buildHypothesisTree` from 12000 to 4000, rerun the benchmark with `--label part1`, and keep the change only if the total candidate count does not drop.

- [ ] **Step 7: Commit** `Run profile walks in parallel and gate after cheap checks`.

---

## Part 2: search objective

### Task 6: Concepts, interest score, padded-fact check

**Files:**
- Create: `Babel/Interest.lean`
- Modify: `Babel/Tests.lean`, `Babel.lean`, `Babel/Gate.lean`

**Interfaces:**
- Produces:
  ```lean
  namespace Babel
  structure StepLimits where
    maxLemmaRepeats : Nat := 1
    maxFactSize : Nat := 400
    simpBudget : Nat := 20000
  structure InterestComponents where
    concepts : Nat := 0
    modules : Nat := 0
    steps : Nat := 0
    joins : Nat := 0
    statementSize : Nat := 0
  def interestScore (c : InterestComponents) : Float
    -- 3.0 * concepts + 2.0 * modules + 1.0 * steps + (if joins > 0 then 2.0 else 0.0) - statementSize / 40.0
  def conceptOf (factType : Expr) : Option Name          -- factType.getAppFn.constName?
  def countDistinct (names : Array (Option Name)) : Nat  -- distinct `some` values
  def defaultSimpContext : MetaM (Simp.Context × Simp.SimprocsArray)
    -- Simp.Context.mkDefault and #[← Simp.getSimprocs]
  def simplifiedSize? (e : Expr) (budget : Nat) : MetaM (Option (Expr × Nat))
    -- result of `Meta.simp e` under `budget` heartbeats with the default context; none on timeout or exception
  def isPaddedFact (e : Expr) (budget : Nat := 20000) : MetaM Bool
    -- true iff simplification yields `True` or an expression with exprSize smaller than exprSize e
  ```
- `closedBySimp` in `Babel/Gate.lean` switches to `defaultSimpContext` (context and simprocs).

- [ ] **Step 1: Write failing checks** in `Babel/Tests.lean` (add `import Babel.Interest`, `import Mathlib.Data.Set.Basic`, `open Lean Meta Elab Term`):

```lean
#guard interestScore { concepts := 3, modules := 2, steps := 5, joins := 1, statementSize := 80 } == 18.0
#guard interestScore { concepts := 4, modules := 2, steps := 5, joins := 0, statementSize := 80 } >
       interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, statementSize := 80 }
#guard interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, statementSize := 400 } <
       interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, statementSize := 80 }
#guard countDistinct #[some `A, none, some `B, some `A] == 2

/-- Apply `k` to the body of a closed `∀` statement given as syntax. -/
def onBody (stx : TermElabM Syntax) (k : Expr → MetaM Bool) : TermElabM Bool := do
  let e ← instantiateMVars (← elabType (← stx))
  forallTelescope e fun _ body => k body

/-- info: true -/
#guard_msgs in
#eval onBody `(∀ (α : Type) (s t : Set α), s ∩ s ⊆ t) (isPaddedFact ·)

/-- info: false -/
#guard_msgs in
#eval onBody `(∀ (α : Type) (s t : Set α), s ⊆ t) (isPaddedFact ·)
```

- [ ] **Step 2: Run** `~/.elan/bin/lake build BabelTest`. Expected: fails, `Babel.Interest` not found.

- [ ] **Step 3: Implement `Babel/Interest.lean`** and switch `closedBySimp`.

- [ ] **Step 4: Run** `~/.elan/bin/lake build Babel Corpus walk BabelTest`. Expected: builds.

- [ ] **Step 5: Commit** `Add interest score and padded-fact check, give the simp gate a real simp set`.

### Task 7: Step-level checks

**Files:**
- Modify: `Babel/Generator.lean`, `Babel/Walk.lean`, `scripts/bench_walk.py` (no change expected), `Babel/Tests.lean`

**Interfaces:**
- Consumes: `StepLimits`, `isPaddedFact`, `exprSize`, `StatsRef`.
- Produces:
  - `WalkStep` gains `concept : Option Name` (from `conceptOf factType`).
  - `tryApplyLemma` gains `limits : StepLimits`. New behaviour, in this order:
    1. Pass 1 never fills a premise with a proof term that already fills another explicit premise of the same application (this includes the target fact). Track the proofs used so far in the application.
    2. In `mkStep`, after `args` are instantiated: if two explicit `Prop`-typed arguments are syntactically equal, reject with `selfReuse`.
    3. If the lemma already occurs `limits.maxLemmaRepeats` times among the ancestors (inclusive) of the steps this application consumes, reject with `repeatedLemma`. Add `def ancestorLemmas (allSteps : Array WalkStep) (parents : Array Nat) : Array Name`.
    4. If `exprSize concl > limits.maxFactSize`, reject with `sizeCap`.
    5. If `isPaddedFact concl limits.simpBudget`, reject with `paddedFact`.
  - `WalkCandidate` gains `checks : (simpNormal : Bool) × (premiseReuse : Nat)` as two fields `simpNormal`, `premiseReuse`, recomputed in `finishWalk` on the final conclusion and over the retained steps, and emitted as `"checks": {"simp_normal": bool, "premise_reuse": n}`.
  - `walk` gains `--max-lemma-repeats N` (default 1) and `--max-statement-size N` (default 400).

- [ ] **Step 1: Write the failing check.** The failing test is the strict benchmark on the padded module:

```bash
.venv/bin/python scripts/bench_walk.py --label t7-before --strict
```
Expected: exit 1 with `lemma_repeated` violations (current behaviour). Delete `docs/superpowers/specs/bench/t7-before.json` afterwards.

Also add to `Babel/Tests.lean`:

```lean
#guard ancestorLemmas
  #[{ (default : WalkStep) with stepIdx := 0, lemmaName := `A, parentSteps := #[] },
    { (default : WalkStep) with stepIdx := 1, lemmaName := `B, parentSteps := #[0] },
    { (default : WalkStep) with stepIdx := 2, lemmaName := `C, parentSteps := #[] }]
  #[1] == #[`B, `A]
```

- [ ] **Step 2: Implement** the five checks, the new fields, and the two flags.

- [ ] **Step 3: Run** `~/.elan/bin/lake build Babel Corpus walk BabelTest`, then `.venv/bin/python scripts/bench_walk.py --label t7 --strict --max-statement-size 400`.
  Expected: exit 0 (no violations). Low yield is acceptable at this point, since the search still stops at the first derivation that meets the old depth rule; calibration happens in Task 9. Delete `t7.json` after reading it.

- [ ] **Step 4: Commit** `Reject self-reuse, repeated lemmas, padded and oversized facts at each step`.

### Task 8: Closed kept derivations and best-of-walk search

**Files:**
- Modify: `Babel/Generator.lean`, `Babel/Gate.lean`, `Babel/Tests.lean`

**Interfaces:**
- Consumes: `InterestComponents`, `interestScore`, `countDistinct`, `StepLimits`, `StatsRef`, `Reject`.
- Produces:
  ```lean
  structure SpecialistSearch where
    focus : Name
    minSteps : Nat := 4
    minConcepts : Nat := 3
    trialsPerWalk : Nat := 240
    keep : Nat := 3
    limits : StepLimits := {}

  structure KeptDerivation where
    stmtClosed : Expr
    proofClosed : Expr
    nBinders : Nat
    stepLabels : Array (Nat × Name × String)      -- retained steps: index, lemma, namespace
    edges : Array (Nat × Nat × Name)              -- parent, child, lemma
    components : InterestComponents
    score : Float
    specialistSymbols : Array Name
    stmtHash : String
  deriving Inhabited

  def closeDerivation (ctxFVars : Array Expr) (steps : Array WalkStep)
      (specialist : Option SpecialistSearch) (stats : StatsRef) : MetaM (Option KeptDerivation)
  def insertKept (kept : Array KeptDerivation) (k : KeptDerivation) (cap : Nat) : Array KeptDerivation
  def renderStandaloneClosed (thmName : String) (stmtClosed proofClosed : Expr) (nBinders : Nat)
      (stepLabels : Array (Nat × Name × String)) (convoluteDepth seed : Nat)
      (explicitStatement : Bool := false) : MetaM (Option (String × String × String))
  def gateKept (kept : KeptDerivation) (seed stepsRequested exactBudget aesopBudget convoluteDepth : Nat)
      (hardLevel2 : Bool) (seen : Std.HashSet String) (rng : Rng) (stats : StatsRef) :
      MetaM (Option WalkCandidate × Rng)
  ```
  - `closeDerivation` does only cheap work: retained steps via `proofShape`, hypothesis pruning, `mkForallFVars` and `mkLambdaFVars` over the kept variables, the metavariable check, components and score. In specialist mode it returns `none` and records `fewSteps`, `fewConcepts` or `noFocusSymbol` when retained steps `< minSteps`, distinct concepts on the retained path `< minConcepts`, or no symbol of the conclusion is defined under `focus`. `components.modules` counts distinct defining modules of the retained lemmas (`definingModule`). `nBinders` is the number of kept variables.
  - `insertKept` keeps the array sorted by descending score, drops an entry whose `stmtHash` is already present, keeps the earlier entry on equal scores, and truncates to `cap`.
  - `renderStandaloneClosed` replaces `renderStandaloneLean`. It opens exactly `nBinders` binders of `stmtClosed` and `proofClosed`, taking binder names and binder info from the `forallE` nodes.
  - `gateKept` runs, in order: duplicate hash (`seen`), `renderStandaloneClosed` (`unrenderable`), convolution inside `forallBoundedTelescope stmtClosed (some nBinders)` with the proof instantiated by `Expr.beta`, kernel `check` (`kernelCheck`), axioms (`badAxioms`), `exact?` (`closedByExact`), then when `hardLevel2` is true `simp` (`closedBySimp`) and `aesop` (`closedByAesop`) as rejections. When `hardLevel2` is false the Level 2 result is only recorded, as today. It fills `checks` and the new `WalkCandidate` field `interest : InterestComponents × Float` (two fields `components`, `interestScore`).
  - `finishWalk` (default walk) becomes `closeDerivation … none` followed by `gateKept … (hardLevel2 := false)`.
  - `LemmaIndex` gains `conclHead : Std.HashMap Name Name`, filled in `buildLemmaIndex`.
  - `runSpecialistLoop` returns `MetaM Unit`, takes `kept : IO.Ref (Array KeptDerivation)`, and at every node calls `closeDerivation` and `insertKept` (cap `search.keep`) and never calls a gate. It stops only when `steps.size >= maxSteps` or the trial budget is spent. When choosing a lemma from a pool it draws up to four with the `Rng` and takes the first whose `conclHead` differs from the source fact's concept, falling back to the first drawn.
  - `runSingleWalk` in specialist mode runs the loop, then calls `gateKept … (hardLevel2 := true)` on the kept derivations in order and returns the first that passes.

- [ ] **Step 1: Write failing checks** in `Babel/Tests.lean`:

```lean
private def kd (hash : String) (score : Float) : KeptDerivation :=
  { (default : KeptDerivation) with stmtHash := hash, score := score }

#guard (insertKept (insertKept (insertKept #[] (kd "a" 1.0) 2) (kd "b" 3.0) 2) (kd "c" 2.0) 2).map (·.stmtHash)
  == #["b", "c"]
#guard (insertKept (insertKept #[] (kd "a" 1.0) 3) (kd "a" 9.0) 3).size == 1
#guard (insertKept (insertKept #[] (kd "a" 2.0) 3) (kd "b" 2.0) 3).map (·.stmtHash) == #["a", "b"]

/-- A conclusion that is itself a `∀` must stay in the conclusion (Review Focus 1). -/
def renderForallConclusion : TermElabM Bool := do
  let stmt ← instantiateMVars (← elabType (← `(∀ (α : Type) (s : Set α), s ⊆ s → ∀ x ∈ s, x ∈ s)))
  let proof ← instantiateMVars (← elabTerm (← `(fun (α : Type) (s : Set α) (h : s ⊆ s) => fun x hx => h hx)) (some stmt))
  let some (decl, _, _) ← renderStandaloneClosed "akcm_candidate" stmt proof 3 #[] 0 0
    | return false
  return (decl.splitOn "(h : s ⊆ s)").length == 2 && (decl.splitOn "∀ x ∈ s, x ∈ s").length == 2

/-- info: true -/
#guard_msgs in
#eval renderForallConclusion
```

- [ ] **Step 2: Run** `~/.elan/bin/lake build BabelTest`. Expected: fails, unknown identifiers.

- [ ] **Step 3: Implement** the interface above. Remove `renderStandaloneLean` and the depth-and-join acceptance from the specialist path. `SpecialistProgress` and `recordProgress` stay as they are.

- [ ] **Step 4: Run** `~/.elan/bin/lake build Babel Corpus walk BabelTest`. Expected: builds.

- [ ] **Step 5: Run** `.venv/bin/python scripts/pipeline.py --seed 20261124 --count 1 --offline`, then `.venv/bin/python scripts/verify.py` on any result it saved. Expected: the default walk still produces a result that verifies. Revert `results/` and `state/` afterwards.

- [ ] **Step 6: Commit** `Keep the best derivations of a walk and gate only those`.

### Task 9: Flags, emitted fields, profile knobs, Part 2 benchmark

**Files:**
- Modify: `Babel/Walk.lean`, `scripts/walk_runner.py`, `scripts/wander.py`, `scripts/pipeline.py`, `scripts/test_akcm.py`
- Create: `docs/superpowers/specs/bench/part2.json`

**Interfaces:**
- `walk` flags: `--min-concepts N` (default 3), `--keep N` (default 3). `--min-proof-depth N` sets `SpecialistSearch.minSteps`. The validity check becomes `3 <= minSteps < maxSteps` and `minConcepts >= 2`.
- Candidate JSON gains `"interest": {"score": f, "concepts": n, "modules": n, "steps": n, "joins": n, "statement_size": n}`.
- `run_walk` gains keyword arguments `min_concepts: int = 3`, `max_lemma_repeats: int = 1`, `max_statement_size: int = 400`, `keep: int = 3`, passed through when `focus` is set.
- `TopicProfile` gains `min_concepts: int = 3`, `max_statement_size: int = 400`. `min_proof_depth` now means minimum retained steps, default 4. `_mutate_knobs` draws `min_concepts` from `(3, 3, 4)` and `min_proof_depth` from `min_depth_range`, whose default becomes `(4, 6)`.
- `_walk_mutated_profile` retries with `min_concepts` relaxed by one, down to 2, in place of the proof-depth relaxation, and uses `timeout=240`.
- `prepare_result` copies `interest` and `checks` from the candidate into `meta` when present.
- `BENCH_ARGS` gains `min_concepts=3`, and `min_proof_depth` becomes 4.

- [ ] **Step 1: Write the failing test.**

```python
def test_profile_knobs_and_meta_carry_interest() -> None:
    base = TopicProfile("Mathlib.Order.Zorn", "Mathlib.Order", "Order", 30)
    assert base.min_concepts == 3 and base.min_proof_depth == 4
    mutated = _mutate_knobs(base, random.Random(1), mutation_kind="explore", allow_convolution=False)
    assert mutated.min_concepts in (3, 4) and 4 <= mutated.min_proof_depth <= 6
    candidate = {"statement_hash": "h", "statement_lean": "theorem akcm_candidate : True",
                 "lean_file": "theorem akcm_candidate : True := trivial\n",
                 "interest": {"score": 21.5, "concepts": 4}, "checks": {"simp_normal": True, "premise_reuse": 0}}
    with patch("pipeline.verify_lean_file", return_value=(True, [], "")):
        meta, _ = prepare_result(candidate, result_id="AKCM-2026-0099", seed=1, interdisciplinary=2.0,
                                 focus="Mathlib.Order", toolchain="leanprover/lean4:v4.36.0")
    assert meta["interest"]["score"] == 21.5 and meta["checks"]["simp_normal"] is True
```

- [ ] **Step 2: Run** the suite. Expected: fails on `min_concepts`.

- [ ] **Step 3: Implement** the flags, fields and knobs.

- [ ] **Step 4: Run** the suite and the Lean build, then
  `.venv/bin/python scripts/bench_walk.py --label part2 --strict --min-concepts 2 --max-statement-size 400`.
  Expected: exit 0; `part2.json` shows zero violations and meets the yield floor from the spec: `valid_candidates >= 4` and `modules_with_valid >= 2`. If the floor is missed, apply these calibrations one at a time, rerunning after each, and stop at the first that meets it: `SpecialistSearch.keep` 3 to 6; `BENCH_ARGS` `trials_per_walk` 180 to 320; `maxFactSize` 400 to 600 to 800; default `min_concepts` 3 to 2 (in `walk`, `run_walk`, `TopicProfile` and the test). Do not loosen the repetition cap, the padded-fact check or the hard Level 2 gate. If the floor is still missed, stop and report the rejection statistics instead of redefining `conceptOf`. Record which calibrations were applied in the commit message. Timing: `seconds_per_valid_candidate` is below the baseline's, or, when the baseline's is `null`, total `wall_seconds` does not exceed the baseline's.

- [ ] **Step 5: Read three candidates** from the `.tmp/` output of the Filter run and check by eye that no subterm of the form `x ∩ x`, `x ∪ x` or `x \ x` appears. If one does, the padded-fact check has a hole: add the statement as a `#guard_msgs` case to `Babel/Tests.lean`, fix `isPaddedFact`, and rerun Step 4.

- [ ] **Step 6: Commit** `Expose concept and size knobs and record the Part 2 benchmark`.

---

## Part 3: the reviewer picks

### Task 10: Screening and a precomputed Referee A

**Files:**
- Modify: `scripts/editorial.py`, `scripts/test_akcm.py`

**Interfaces:**
- Produces:
  ```python
  def scale_interest(score: float) -> float            # max(0.0, min(10.0, score / 4.0))
  def screen_candidate(candidate: dict[str, Any], *, cfg: dict[str, Any], offline: bool = False) -> dict[str, Any]
  def process_editorial(meta, *, offline=False, cfg=None, families_state=None,
                        referee_a: dict[str, Any] | None = None) -> dict[str, Any]
  ```
  `screen_candidate` returns `{"score": float, "tie_break": float, "source": "referee_a" | "interest_score", "verdict": dict | None}`. It calls `run_decider` with `referee_id="Referee A"`, `decider_1_model`, the same persona note and `persona_bias=1` that `process_editorial` uses, on a dict built from the candidate with `interdisciplinarity = len(namespaces)`. From the verdict: `score = decision_metrics.expected_score` when present, otherwise `float(importance)`; `tie_break = decision_metrics.p_human_cares` when present, otherwise `0.0`. With `offline=True`, with no API key, or on `LLMError`: `score = scale_interest(candidate.get("interest", {}).get("score", 0.0))`, `tie_break = 0.0`, `source = "interest_score"`, `verdict = None`.
  `process_editorial` uses `referee_a` as `ref1` when it is given and does not call the model for Referee A.
  `_candidate_summary_for_llm` and the namer's user prompt in `run_namer` use `meta.get("statement_pretty") or meta["statement_lean"]` (the namer keeps its 400-character cut). No prompt file changes.

- [ ] **Step 1: Write the failing tests.**

```python
def test_screening_uses_referee_and_falls_back() -> None:
    cfg = {"llm": {"endpoint": "e", "decisions_endpoint": "d", "decider_1_model": "gemini-decision-1"}}
    candidate = {"statement_lean": "theorem t : True", "statement_hash": "h", "steps_taken": 5,
                 "namespaces": ["Filter"], "dependencies": {"nodes": [], "edges": []},
                 "novelty": {"level_3_ratio": 2.0}, "interest": {"score": 22.0}}
    answers = {"kind": {"choice": "Lemma"}, "importance": {"score": 5.4, "confidence": 0.5},
               "msc_section": {"choice": "54"}, "surprising": {"noul": 0.2}, "human_cares": {"noul": 0.31}}
    with patch("editorial.resolve_api_key", return_value="k"), \
         patch("editorial.gemini_decisions", return_value=answers):
        live = screen_candidate(candidate, cfg=cfg)
    assert live["source"] == "referee_a" and live["score"] == 5.4 and live["tie_break"] == 0.31
    assert live["verdict"]["model"] == "gemini-decision-1"
    with patch("editorial.resolve_api_key", return_value="k"), \
         patch("editorial.gemini_decisions", side_effect=LLMError("down")):
        failed = screen_candidate(candidate, cfg=cfg)
    assert failed == {"score": 5.5, "tie_break": 0.0, "source": "interest_score", "verdict": None}
    no_interest = screen_candidate({k: v for k, v in candidate.items() if k != "interest"}, cfg=cfg, offline=True)
    assert no_interest["score"] == 0.0 and no_interest["source"] == "interest_score"
    assert scale_interest(100.0) == 10.0 and scale_interest(-3.0) == 0.0
    readable = candidate | {"statement_pretty": "∀ {α : Type} (s : Set α), s ⊆ s"}
    summary = _candidate_summary_for_llm(readable | {"interdisciplinarity": 1})
    assert "s ⊆ s" in summary and "theorem t : True" not in summary
    assert "theorem t : True" in _candidate_summary_for_llm(candidate | {"interdisciplinarity": 1})

def test_precomputed_referee_a_is_reused() -> None:
    # Build a minimal verified meta (as in test_gemini_decision_1_referee), a temp ROOT with
    # state/families.json and state/blocklist.json, and call process_editorial(..., offline=True,
    # referee_a={"referee_id": "Referee A", "model": "gemini-decision-1", "kind": "Theorem",
    #            "importance": 7, "msc_code": "54A05", "justification": "kept"}).
    assert editorial["referees"][0]["justification"] == "kept"
    assert editorial["referees"][0]["model"] == "gemini-decision-1"
    assert editorial["referees"][1]["model"] == "offline-heuristic-referee"
```

- [ ] **Step 2: Run** the suite. Expected: `ImportError` for `screen_candidate`.

- [ ] **Step 3: Implement.**

- [ ] **Step 4: Run** the suite. Expected: pass.

- [ ] **Step 5: Commit** `Screen candidates with Referee A and reuse the verdict`.

### Task 11: Ranking, selection, candidate log

**Files:**
- Create: `scripts/selection.py`
- Modify: `scripts/test_akcm.py`

**Interfaces:**
- Produces:
  ```python
  @dataclass
  class PoolEntry:
      candidate: dict[str, Any]
      profile: TopicProfile
      batch_seed: int
      screening: dict[str, Any]

  def rank_pool(pool: list[PoolEntry]) -> list[PoolEntry]
      # sort by (-score, -tie_break, statement_hash)
  def select_and_verify(ranked: list[PoolEntry], *, count: int, module_cap: int = 2,
                        verify: Callable[[PoolEntry], Any | None]) -> tuple[list[tuple[PoolEntry, Any]], dict[str, str]]
      # walks the ranking; skips an entry whose module already has module_cap accepted results
      # (outcome "outranked"); calls verify; None -> "failed_verification"; otherwise accepted
      # ("published"). Stops calling verify once `count` are accepted; the rest are "outranked".
      # Returns accepted pairs in rank order and outcome by statement_hash.
  def publish_limit(count: int, pool_size: int) -> int        # min(count, ceil(pool_size / 2))
  def log_record(entry: PoolEntry, *, rank: int, pool_size: int, outcome: str) -> dict[str, Any]
      # keys: statement_hash, statement_pretty, module, focus, interest, score, tie_break, source,
      #       rank, pool_size, outcome
  def append_candidate_log(records: list[dict[str, Any]], *, path: Path, keep: int = 500) -> None
      # appends JSON lines, creating the file if missing, then keeps only the last `keep` lines
  ```

- [ ] **Step 1: Write the failing tests.**

```python
def test_rank_select_and_log() -> None:
    def entry(tag: str, module: str, score: float, tie: float = 0.0, source: str = "referee_a") -> PoolEntry:
        profile = TopicProfile(module, "Mathlib.X", "X", 30)
        return PoolEntry({"statement_hash": tag, "statement_pretty": tag}, profile, 1,
                         {"score": score, "tie_break": tie, "source": source, "verdict": None})
    pool = [entry("d", "M.B", 4.0), entry("a", "M.A", 6.0), entry("b", "M.A", 6.0, 0.4),
            entry("c", "M.A", 5.0), entry("e", "M.C", 5.5, source="interest_score")]
    ranked = rank_pool(pool)
    assert [e.candidate["statement_hash"] for e in ranked] == ["b", "a", "e", "c", "d"]
    verify = lambda e: None if e.candidate["statement_hash"] == "a" else e.candidate["statement_hash"]
    accepted, outcomes = select_and_verify(ranked, count=3, module_cap=1, verify=verify)
    assert [result for _, result in accepted] == ["b", "e", "d"]
    assert outcomes == {"b": "published", "a": "outranked", "e": "published",
                        "c": "outranked", "d": "published"}
    accepted, outcomes = select_and_verify(ranked, count=2, module_cap=2, verify=verify)
    assert [result for _, result in accepted] == ["b", "e"]
    assert outcomes["a"] == "failed_verification" and outcomes["c"] == "outranked"
    assert select_and_verify([], count=3, verify=verify) == ([], {})
    assert [publish_limit(6, n) for n in (0, 1, 2, 5, 24)] == [0, 1, 1, 3, 6]
    with TemporaryDirectory() as directory:
        path = Path(directory) / "candidates.jsonl"
        records = [log_record(e, rank=i + 1, pool_size=5, outcome="outranked") for i, e in enumerate(ranked)]
        assert records[2]["source"] == "interest_score" and records[0]["rank"] == 1
        append_candidate_log(records, path=path, keep=4)
        append_candidate_log(records[:2], path=path, keep=4)
        lines = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]
        assert [line["statement_hash"] for line in lines] == ["c", "d", "b", "a"]
```

- [ ] **Step 2: Run** the suite. Expected: `ImportError` for `selection`.

- [ ] **Step 3: Implement `scripts/selection.py`.**

- [ ] **Step 4: Run** the suite. Expected: pass.

- [ ] **Step 5: Commit** `Add pool ranking, selection and the candidate log`.

### Task 12: Wire the pool into wander and launch, steer the drift

**Files:**
- Modify: `scripts/pipeline.py`, `scripts/wander.py`, `scripts/test_akcm.py`, `.github/workflows/nightly.yml`

**Interfaces:**
- Consumes: `screen_candidate`, `process_editorial(referee_a=…)`, `PoolEntry`, `rank_pool`, `select_and_verify`, `log_record`, `append_candidate_log`, `run_walks_parallel`.
- Produces:
  - `pipeline.py` flag `--pool-factor N` (default 4). `run_wander(..., pool_factor: int, workers: int)` and `run_launch(..., pool_factor: int, workers: int)`.
  - `run_wander` sequence: mutate profiles; request `ceil(pool_factor * count / len(profiles))` candidates from each profile in parallel; drop duplicates within the pool and hashes already in `results/`; `screen_candidate` each; `rank_pool`; `select_and_verify(count=publish_limit(count, len(ranked)), module_cap=2)` with a `verify` that calls `prepare_result` using the next free ID and advances the ID only on success; for each accepted pair call `process_editorial(..., referee_a=entry.screening["verdict"])`, set `meta["selection"] = {"pool_size", "rank", "source", "score"}`, and save; append the candidate log to `ROOT / "state" / "candidates.jsonl"`; record exploration with scores. It returns 0 whatever the accepted count.
  - `run_launch` uses the same sequence with `count` unchanged (no `publish_limit`) and keeps its rule: when fewer than `count` verify, it writes nothing (no results, no state, no candidate log) and returns 1.
  - `record_exploration(profiles, *, seed, path, scores: dict[str, dict[str, Any]] | None = None)`. `scores` is keyed by module with `{"pool_size": int, "published": int, "best_score": float | None, "mean_score": float | None}`. `best_score` and `mean_score` are computed only from entries whose `source` is `"referee_a"`, and are `None` when there are none.
  - `wander.focus_scores(wander_state) -> dict[str, float]`: highest non-null `best_score` per focus.
  - In `mutate_profiles`, the drift anchors are ordered by weighted sampling without replacement using the seeded `rng`, with weight `max(0.1, best_score)` for a scored focus and the mean of the known weights (or `1.0` when none is known) for an unscored one. The rest of the function is unchanged.
  - `nightly.yml`: no flag changes are required; add `--pool-factor 4` explicitly to the nightly and launch commands so the cost is visible in the workflow.

- [ ] **Step 1: Write the failing tests.**

```python
def test_drift_prefers_high_scoring_focus_and_tolerates_old_history() -> None:
    pool = [TopicProfile("Mathlib.A.X.One", "Mathlib.A.X", "A", 40),
            TopicProfile("Mathlib.A.X.Two", "Mathlib.A.X", "A", 40),
            TopicProfile("Mathlib.B.Y.One", "Mathlib.B.Y", "B", 40),
            TopicProfile("Mathlib.B.Y.Two", "Mathlib.B.Y", "B", 40),
            TopicProfile("Mathlib.C.Z.One", "Mathlib.C.Z", "C", 40)]
    history = [{"module": "Mathlib.A.X.One", "focus": "Mathlib.A.X", "domain": "A", "best_score": 9.0},
               {"module": "Mathlib.B.Y.One", "focus": "Mathlib.B.Y", "domain": "B", "best_score": 0.2},
               {"module": "Mathlib.C.Z.One", "focus": "Mathlib.C.Z", "domain": "C"}]   # pre-change entry
    assert focus_scores({"history": history}) == {"Mathlib.A.X": 9.0, "Mathlib.B.Y": 0.2}
    drifts = []
    with TemporaryDirectory() as empty:
        for seed in range(200):
            picked = mutate_profiles(seed=seed, n_profiles=3, candidates=pool,
                                     wander_state={"history": history}, results_dir=Path(empty))
            drifts += [p.module for p in picked if p.mutation_kind == "drift"]
    assert drifts.count("Mathlib.A.X.Two") > 3 * drifts.count("Mathlib.B.Y.Two")

def test_wander_publishes_top_of_pool_and_handles_small_pool() -> None:
    # Temp ROOT with state/issues.json, state/families.json, state/blocklist.json (copied),
    # state/wander.json absent, state/candidates.jsonl absent, lean-toolchain.
    # Patch pipeline.mutate_profiles to return two profiles (modules M.A, M.B);
    # pipeline.run_walk to return 3 candidates for M.A (hashes a1, a2, a3) and 1 for M.B (b1);
    # pipeline.verify_lean_file to (True, [], ""); pipeline.screen_candidate to give scores
    # a1=2.0, a2=6.0, a3=5.0, b1=4.0 with source "referee_a".
    assert run_wander(count=3, areas=2, seed=1, max_attempts=5, exact_heartbeats=1, aesop_heartbeats=1,
                      allow_convolution=False, cfg=cfg, offline=True, publish_issue=False,
                      pool_factor=2, workers=2) == 0
    metas = sorted(json.loads(p.read_text()) for p in (root / "results").glob("*/meta.json"), key=lambda m: m["id"])
    assert [m["statement_hash"] for m in metas] == ["a2", "a3"]     # publish_limit(3, 4) == 2
    assert metas[0]["selection"] == {"pool_size": 4, "rank": 1, "source": "referee_a", "score": 6.0}
    log = [json.loads(line) for line in (root / "state" / "candidates.jsonl").read_text().splitlines()]
    assert {r["statement_hash"]: r["outcome"] for r in log} == {
        "a2": "published", "a3": "published", "b1": "outranked", "a1": "outranked"}
    history = json.loads((root / "state" / "wander.json").read_text())["history"]
    assert history[0]["best_score"] == 6.0 and history[0]["published"] == 2 and history[0]["pool_size"] == 3
    # Small and empty pools (Review Focus 3): rerun in a fresh ROOT with run_walk returning
    # WalkRun() for every profile; expect return value 0, no result directories, and an empty log.
```

Extend `test_launch_replaces_issue_only_after_full_verification` with one assertion in its failing branch: `assert not (root / "state" / "candidates.jsonl").exists()`.

- [ ] **Step 2: Run** the suite. Expected: failures on `focus_scores` and on `run_wander`'s new parameters.

- [ ] **Step 3: Implement** the wiring in `pipeline.py` and the drift weighting in `wander.py`.

- [ ] **Step 4: Run** the suite. Expected: pass.

- [ ] **Step 5: Run end to end, offline:**
  `.venv/bin/python scripts/pipeline.py --wander --areas 2 --count 2 --seed 20261126 --offline`
  then `.venv/bin/python scripts/verify.py results/<each new directory>` and `SITE_BASE_PATH="" .venv/bin/python scripts/build_site.py`.
  Expected: at most 2 new results, each verifies, each `meta.json` has `selection.source == "interest_score"`, `state/candidates.jsonl` exists, the site builds. Then revert `results/` and `state/` and remove the new result directories and `state/candidates.jsonl`.

- [ ] **Step 6: Commit** `Publish the top of a referee-ranked pool and steer drift by score`.

### Task 13: Documentation and final benchmark

**Files:**
- Modify: `README.md`, `CLAUDE.md`, `AGENTS.md`
- Create: `docs/superpowers/specs/bench/final.json`

- [ ] **Step 1: Update the docs.** `README.md`: replace the description of the novelty gate and specialist search with the new acceptance rule, the pool-and-rank flow, and the new flags; correct the two stale statements already listed in `CLAUDE.md` (GitHub Models, Pages URL derivation). `CLAUDE.md`: update the Commands section (`lake build BabelTest`, `scripts/bench_walk.py`, `--pool-factor`, `--workers`), the generator and pipeline architecture paragraphs, and the data model (`interest`, `checks`, `selection`, `state/candidates.jsonl`); remove the two items fixed in the README from "Things that are easy to get wrong". `AGENTS.md`: add the Lean test command and the benchmark to the testing section.

- [ ] **Step 2: Run** `.venv/bin/python scripts/test_akcm.py`, `~/.elan/bin/lake build Babel Corpus walk BabelTest`, and `.venv/bin/python scripts/bench_walk.py --label final --strict --min-concepts 2 --max-statement-size 400`.
  Expected: tests pass, build succeeds, benchmark exits 0. In `final.json`, every run has a `stats.dominant_reject` or at least one candidate, the yield floor is met, and the timing criterion from Task 9 Step 4 holds against `baseline.json`.

- [ ] **Step 3: Write the comparison.** Append a "Results" section to the spec with a table of baseline, part1, part2 and final totals (wall seconds, candidates, valid candidates, seconds per valid candidate, violations), and one sentence stating that referee scores remain to be measured in the first week of nightly runs.

- [ ] **Step 4: Commit** `Document the new search and selection, record final benchmark`.

## After merge (not a task for the implementer)

Referee scores can only be observed in GitHub Actions. After a week of nightly runs, compare the mean Referee A expected score and mean Referee B score of the newly published results with two references: the default-walk baselines in the spec (2.58 and 1.14), and the specialist results the nightly job published before the merge. Read Referee B's justifications for mentions of padding.

A manual dispatch of the nightly workflow on the feature branch would exercise screening and verdict reuse against the live referee before merge. It pushes the branch, spends referee calls, and commits results to that branch, so it happens only with the user's explicit go-ahead.
