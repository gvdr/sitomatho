# Design: theorems the reviewer finds interesting

Date: 2026-11-25
Status: draft, awaiting approval

## Intent

The journal's generator should produce theorems that the AI referees rate as interesting. A necessary condition is that a result is not trivial. Today's output fails that condition, and the generator is slow and opaque about why it fails. This design changes what the specialist search looks for, lets the referee choose what gets published, and makes the generator measurable and faster.

## Evidence this design rests on

Live referee verdicts on the seven published results (commit `3e1f646` on `origin/main`):

| Referee | Scores | Mean |
|---|---|---|
| A, `gemini-decision-1`, expected score out of 10 | 3.07, 3.02, 1.75, 1.95, 1.40, 4.46, 2.40 | 2.58 |
| B, `gemini-4-hydrogen`, integer out of 10 | 1, 2, 1, 1, 1, 1, 1 | 1.14 |

Referee B's written complaints fall into two groups.

- Padding: "idempotent self-union ... adding syntactic bulk without any mathematical substance", "baroque nesting of redundant `max` and `min` terms", "nested AddOpposite wrappers are entirely artificial".
- Closure composition: "an artificial specialization ... of a routine closure property", "an immediate corollary of the elementary fact that a finite intersection of clopen sets is clopen".

Two local runs of the current specialist search (`--min-proof-depth 6 --trials-per-walk 180 --max-steps 12 --convolute 0`):

- `Mathlib.Order.Filter.Basic`, focus `Mathlib.Order.Filter`: 4 candidates in 30 s wall time, peak memory 1.5 GB. Every candidate is padded. The depth-10 candidate uses `Filter.union_mem_sup` four times and its statement begins `U ∈ s → ((U ∪ (U \ U) \ U) ∩ (U ∪ (U \ U) \ U) ∪ ...`.
- `Mathlib.RingTheory.Localization.Ideal`, focus `Mathlib.RingTheory.Localization`: 80 attempts, 368 s, zero candidates, although derivations reached depth 10 with a branch join. The log does not say why they were rejected. About 11 s of each run is module loading and lemma indexing.

Mechanisms in the code that produce the padding:

- `tryApplyLemma` fills a lemma's remaining explicit hypotheses from already derived facts, and the fact being extended is among the ones it tries. A closure lemma such as `inter_mem` therefore receives the same fact twice.
- Closure lemmas have a conclusion with the same head predicate as their hypothesis, so they can be applied again without limit.
- `finishWalk` in specialist mode accepts on derivation depth plus one branch join. Neither measures what the statement says.
- `runSpecialistLoop` calls `finishWalk`, including the `exact?`, `simp` and `aesop` gates, at every node that reaches the depth target, and returns the first that passes.
- `closedBySimp` in `Babel/Gate.lean` builds its context with `Simp.mkContext` and passes no lemma set and no simprocs, so the Level 2 `simp` check runs with an empty simp set and closes almost nothing. Padded statements therefore earn the "not routine" badge. The fix is to use `Simp.Context.mkDefault` and the default simprocs, and it is part of Part 2.

- In specialist mode the statement stored as `statement_lean` is printed with `pp.explicit`, `pp.universes` and `pp.proofs` switched on, and `_candidate_summary_for_llm` sends that field to the referees. A statement whose readable form is a few lines reaches the referee as several thousand characters of `@Filter.Eventually.{0} α (fun x ↦ ...`. The seven baseline results came from the default walk, where the field is readable, so no referee has yet read a specialist result in readable form.

## Goals

1. No published statement is padded: the default `simp` set cannot make it smaller, and no fact fills two premises of one lemma.
2. The specialist search prefers a short statement backed by a long derivation that passes through several distinct concepts, and returns the best such derivation it finds within its budget.
3. The referee decides which candidates are published: the pipeline generates a pool larger than needed, ranks it by referee score, and publishes the top of the ranking.
4. Every walk run reports where its time went and why candidates were rejected.
5. A run that is cut off by its time limit keeps the candidates it had already produced.
6. Wall time per accepted candidate on a fixed benchmark goes down, and a benchmark module that yields nothing says why.

## Non-goals

- A new generator. "Generator B" (mutating existing theorems) stays a future milestone.
- New inference moves such as rewriting with equalities, using `Iff` lemmas, or instantiating type variables with concrete types.
- Redesigning the default, non-specialist walk (`runWalkLoop`). It only inherits the step-level checks placed in shared code.
- Changing the baroque proof convoluter, the site, or the namer and gloss.
- Caching the loaded environment or the lemma index between processes.
- Automatic tuning of the interest-score weights from referee data. This design only records the data that would make it possible.

## Anti-goals

- Raising scores by editing the referee prompts, the decision rubric, or the offline heuristic referee. The referees are the measuring instrument and stay as they are. Giving them the readable statement in place of the fully explicit rendering is allowed and is part of this design, because it is the form the baseline referees read.
- Weakening verification. Every published `Result.lean` still passes `scripts/verify.py` with the same axiom allowlist.
- A generator so strict that nights routinely produce nothing. The weekly issue must still fill.
- Losing reproducibility: a given seed, toolchain and set of flags must still produce the same candidates from `lake exe walk`.

## Constraints

- Lean `v4.36.0` and Mathlib `v4.36.0`, pinned.
- No LLM API key exists on the development machine. Referee scores can be observed only in GitHub Actions. All local development and all tests must work with `--offline`.
- GitHub Actions job limit of 90 minutes for the nightly run; one walk process peaks around 1.5 GB of memory.
- `scripts/test_akcm.py` is assertion-based with no pytest; new tests are registered in its main block.
- The `meta.json` files already published must keep rendering. New fields are additive.

## Approaches considered

**A. Tighten the gate.** Reject a finished candidate when `simp` shrinks its statement, when one fact fills two premises, or when `simp` or `aesop` closes it. This is a small change in `finishWalk`. It answers the padding complaint only, leaves closure compositions as the typical output, and lowers yield because the search still spends its budget building padded derivations that are then thrown away.

**B. Change what the search looks for.** Apply the checks from A at every step so padded branches are cut where they start, prefer steps that move to a different predicate, and keep the best derivation of a walk according to a cheap interest score. This is a medium rewrite of the specialist loop. It answers both complaints and cuts wasted search.

**C. Let the reviewer pick.** Generate more candidates than needed, score each with the decision-model referee, publish the top few, and steer module choice by past scores. This is mostly Python and optimises the stated goal directly. On its own it can only select the least bad of what the generator makes, and it costs one referee call per candidate.

**Chosen: B, then C.** The user picked this after seeing the three options. B changes what exists to be selected and C then selects with the real target. A is contained in B.

## Design

The work has three parts, built in this order. Each part leaves the pipeline working.

### Part 1: measurement and plumbing

**Walk statistics.** `lake exe walk` records and reports:

- wall time per phase: module import, lemma index, hypothesis tree, search, gates (`exact?`, `simp`, `aesop` separately), rendering;
- a counter per rejection reason, at step level (self-reuse, repeated lemma, padded fact, size cap, no unifier, heartbeat limit) and at candidate level (too few concepts, no focus symbol, kernel check failed, bad axioms, closed by `exact?`, closed by `simp`, closed by `aesop`, unrenderable statement, duplicate hash);
- attempts made, lemma applications tried, lemma applications that succeeded.

The statistics go to stderr as a summary and into the output file, so the pipeline can log them and tests can read them.

**Incremental output.** The output file is valid and complete after every accepted candidate. When the pipeline's timeout expires it kills the process and reads what is there. `run_walk` returns the partial list with a flag that the run was cut short.

**Parallel modules.** `run_wander` and `run_launch` start the walks for their profiles concurrently, bounded by a worker count that defaults to half the available CPUs and can be set by flag. Results are consumed in profile order so that ID assignment and acceptance stay deterministic for a given seed. Verification and editorial stay sequential.

**Benchmark.** A script runs a fixed list of module, focus and seed combinations (the four `LAUNCH_PROFILES` with two seeds each) and prints, per run, wall time, candidates, the statistics above, and the invariants from Goal 1 checked against the output. It is run before Part 2 to record a baseline and after each later part. The baseline numbers are written into this folder next to the design.

Fixing the largest cost that the statistics reveal is part of this work. The suspected costs, to be confirmed by the measurement, are the gates being run on every qualifying node and the gates being run before the cheap rendering check.

### Part 2: search objective

**Step-level checks, in shared `tryApplyLemma` or its callers, so both walks get them:**

- One fact per premise. A derived fact or local hypothesis may fill at most one explicit premise of a lemma application.
- Lemma repetition cap. A lemma may appear at most once on the retained path of a derivation. The cap is a parameter with default 1.
- Padded facts. After a step produces a new fact, its statement is simplified with the default `simp` set under a small heartbeat budget. If the result is `True` or has fewer expression nodes than the original, the step is rejected. A timeout counts as not padded.
- Size cap. A step is rejected when the new fact's statement exceeds a node-count cap. The cap is a parameter.

**What a candidate must satisfy in specialist mode (replaces "depth at least N and one join"):**

- at least `min-steps` retained steps;
- at least `min-concepts` distinct concepts on the retained path, where the concept of a step is the head constant of its fact's statement, and the default minimum is 3;
- the final statement mentions a symbol defined under the focus module prefix (unchanged);
- the kernel check and axiom check pass (unchanged);
- `exact?` does not close it (unchanged), and neither `simp` nor `aesop` closes it. Level 2 becomes a hard gate in specialist mode. The badge fields stay in the output.

A branch join is no longer required. It contributes to the score.

**Interest score.** A cheap number computed from a derivation without running any gate. It increases with distinct concepts, with distinct defining modules among the lemmas used, with retained steps, and with the presence of a join. It decreases with the node count of the final statement. The components and default weights live in one place in the Lean code and are emitted with each candidate (`interest_score` plus the raw components), so they can be compared with referee scores later.

**Search loop.** Within one walk's trial budget the loop explores as today but no longer stops at the first qualifying derivation. It keeps the best-scoring qualifying derivation seen so far. Lemma choice at each step favours lemmas whose conclusion has a different head constant from the hypothesis they consume, using the existing specialist and ambient indexes. When the budget is spent, the expensive gates run on the kept derivation only, in order of cost: rendering check, kernel and axiom check, `exact?`, `simp`, `aesop`. If it fails a gate, the next best kept derivation is tried, up to a small fixed number.

**Command line.** `walk` gains flags for the minimum concept count, the repetition cap, the statement size cap, and the number of fallback derivations per walk. `--min-proof-depth` keeps working and means minimum retained steps. `TopicProfile` in `scripts/wander.py` and `_mutate_knobs` mutate the new knobs in place of proof depth. The depth-relaxation retry in `_walk_mutated_profile` relaxes the concept minimum by one, down to 2.

**Reproducibility.** All randomness stays on the threaded `Rng`. Heartbeat budgets, not wall-clock limits, bound every check inside Lean, so results do not depend on machine speed.

### Part 3: the reviewer picks

**Pool, then screen, then verify.** For a target of `count` published results, `run_wander` asks the walks for a pool of `pool-factor × count` candidates in total (default factor 4), spread over the profiles. It removes duplicates and already published hashes, then screens every remaining candidate with Referee A before any standalone verification, since a referee call takes about a second and a verification takes much longer. Candidates are ranked by Referee A's expected score, with the probability that a human cares as the tie-break. Verification then proceeds down the ranking until `count` results have passed. A cap of two published results per module keeps one productive module from filling an issue.

**How much is published.** In `run_wander` the number published is `min(count, ceil(pool_size / 2))`, where `pool_size` is the number of screened candidates. At most half of a pool is published, so the referee's ranking always decides something, and a pool of one still publishes one. `run_launch` is exempt: it needs its full count.

**What the editorial desk reads.** The referees, the namer and the gloss receive `statement_pretty` when the record has one and fall back to `statement_lean` otherwise. `statement_lean` and `Result.lean` keep the explicit form, which is what makes the standalone file re-elaborate. The site keeps showing what it shows today.

**No second opinion on the same call.** The screening verdict is reused as Referee A's report in the editorial record. `process_editorial` accepts a precomputed Referee A verdict and then runs Referee B, the namer and the gloss only for results that will be published.

**Offline and failure behaviour.** With `--offline`, with no API key, or when a screening call fails, the candidate is ranked by the generator's `interest_score` scaled into the referee's range. A run never fails because the referee is unavailable. The record shows which ranking source was used.

**Steering module choice.** Each entry appended to `state/wander.json` gains the pool size, the number published, and the best and mean screening score for that profile. `mutate_profiles` keeps its exploration slots weighted by inverse visit count and changes the drift slot: its anchor is drawn from recent focuses with weight proportional to their best screening score, in place of a uniform draw. Entries without a score (older history, offline runs) get a neutral weight.

**Candidate log.** Every screened candidate, published or not, is appended to `state/candidates.jsonl` with its statement hash, pretty statement, module, focus, interest-score components, screening scores, ranking source, and outcome (published, outranked, failed verification). The file is trimmed to the most recent 500 lines. It is the data set for judging later whether the interest score predicts the referee.

**Metadata.** A published `meta.json` gains `interest` (score and components) and `selection` (pool size, rank, ranking source, screening score). Templates are untouched in this design.

**Launch path.** `run_launch` uses the same pool, screen and verify sequence, keeping its rule that nothing is written unless the full count verifies.

## How success is judged

Measured locally with the benchmark, offline:

- zero candidates violate the Goal 1 invariants;
- every benchmark run ends with a statistics summary, and a run with zero candidates names its dominant rejection reason;
- wall seconds per valid candidate is lower than the recorded baseline, where a valid candidate is one with no invariant violation. Padded baseline candidates therefore do not count for the baseline. If the baseline has no valid candidate, the criterion is that the final benchmark has some and that its total wall time does not exceed the baseline's;
- no benchmark run exceeds the pipeline timeout without output;
- yield floor used for calibration: at least 4 valid candidates across the eight benchmark runs, coming from at least 2 of the 4 modules;
- `scripts/test_akcm.py` passes, with new tests for ranking and selection, reuse of the screening verdict, partial output after a timeout, deterministic consumption order under parallel walks, the score-weighted drift, and the candidate log trim.

Measured in GitHub Actions after merge, since that is where the referees run:

- across the first week of nightly runs, the mean Referee A expected score of published results is above the 2.58 baseline and the mean Referee B score is above 1.14;
- Referee B's justifications for those results do not describe padding or redundant terms.

The second group is the real target and cannot be guaranteed by construction. If the first week shows no improvement, the candidate log is the starting point for the next iteration.

The 2.58 and 1.14 baselines come from default-walk results. The nightly job publishes specialist results, so results it publishes between now and the merge are the closer comparison, with the caveat that their referees read the explicit rendering. Both comparisons are reported. A manual run of the nightly workflow on the feature branch would give a cleaner before and after; it spends live referee calls and needs the user's go-ahead.

## Decisions made by the author, open to correction

These were not discussed with the user and are proposals.

- Low-scoring pool candidates are dropped and only logged; the top `count` are published whatever their absolute score, so the weekly issue always fills.
- Pool factor 4, module cap 2, concept minimum 3, repetition cap 1, candidate log length 500.
- "Concept" is the head constant of a step's statement.
- "Padded" means `simp` yields `True` or a smaller expression.
- Level 2 becomes a hard gate in specialist mode.
- The editorial desk reads the readable statement, as described under Part 3.
- Wander publishes at most half of the screened pool.
- When yield is below the floor, the settings give way in this order: derivations kept per walk, trials per walk, statement size cap, concept minimum from 3 to 2. The repetition cap of 1, the padded-fact check and the hard Level 2 gate do not give way. Redefining "concept" is a last resort and would be raised with the user first.
- The nightly `count` stays at 6 and the walk timeout rises from 120 s to 240 s.
- Screening uses Referee A only. Referee B is not used for selection, to keep cost at one decision call per candidate.
- The site does not display the new metadata yet.
- The design document and baseline numbers are left uncommitted until the user asks for a commit.

## Left to the builder

- Exact flag names, score weights, heartbeat budgets and size caps, calibrated against the benchmark so that yield stays usable.
- The output file layout that carries candidates plus statistics while remaining valid after each append, and the matching reader in `run_walk`.
- How the search keeps its best derivations given that facts live inside nested `withLocalDecl` scopes (closing over the context at the point of discovery is the expected route).
- The concurrency primitive for parallel walks.
- Which measured cost to fix first in Part 1.
- Updating `README.md`, `CLAUDE.md` and `AGENTS.md` where commands or behaviour change.

## Risks

- The `simp` check on every step may cost more than the search it saves. The statistics will show this; the fallback is to run it only on facts that grew.
- Head-constant concepts may be too coarse in some areas (many facts share the head `Eq` or `LE.le`). The benchmark covers four different areas so that this shows up early; a refinement would use the head of the main argument for such relations.
- With padding removed, some modules may yield nothing at the default settings. The relaxation retry and the per-run rejection summary are there to make that visible and recoverable.
- Selecting by referee score rewards whatever the referee happens to like. That is the stated aim of the project, and the anti-goal on editing referee prompts keeps the instrument fixed.

## Results

Measured on the development machine with `scripts/bench_walk.py` (four modules, two seeds each, offline). Summaries are in `bench/`.

| Run | Wall time | Search time | Candidates | Valid | Modules with a valid candidate | Seconds per valid candidate | Violations |
|---|---|---|---|---|---|---|---|
| `baseline` (before any change) | 446.6 s | 111.2 s | 10 | 3 | 2 | 148.9 | 13 |
| `part1` (measurement, enforced budgets) | 210.1 s | 155.7 s | 11 | 3 | 2 | 70.0 | 15 |
| `part2` (new search) | 160.9 s | 123.1 s | 12 | 12 | 3 | 13.4 | 0 |
| `final` (after the review fixes) | 113.7 s | 77.2 s | 11 | 11 | 3 | 10.3 | 0 |

A valid candidate has no invariant violation. The baseline and `part1` rows could only be checked for repeated lemmas, since those runs did not emit the other fields, so their valid counts are generous. Wall time includes module loading, which varied with the page cache; search time is the comparable figure. One baseline run was killed at 300 s without statistics, so the baseline search time is understated.

What the measurement showed, beyond what the design assumed:

- The heartbeat budgets in the walk were not enforced, so `exact?` ran unbounded. Enforcing them accounts for most of the wall-time drop in `part1`.
- The walk had never introduced a new variable or hypothesis: the code that was meant to do it failed a scope check silently. Multi-premise lemmas could only fire by reusing facts already present, which is what produced `s ∩ s`. Lemma applications now open new binders, and statements carry several hypotheses over several objects.
- `Mathlib.Topology.Sheaves.MayerVietoris` yields nothing under the new rules, with `unresolved` as its dominant rejection: its lemmas need premises the walk cannot supply.

Changes to the design made during the work, each recorded as a ruling in the execution ledger and listed in the hand-over:

- A fact matches a lemma hypothesis only up to instance-reducible unfolding.
- Glue lemmas (logical, basic order and basic set vocabulary), deprecated aliases and auto-generated congruence lemmas are left out of the index.
- "Padded" is measured on the visible size of a statement (explicit arguments only), and also covers sets in unfolded form.
- The interest score gained a focus component and counts length up to six steps.
- Referee-scored candidates always rank ahead of fallback-ranked ones.

### Live run on the feature branch

One manual run of the nightly workflow on `interesting-theorems` (2026-11-24, `count=6`, `convolute=4`, Actions run 45511029489, results in commit `4546363`, reverted afterwards so the branch merges cleanly). It took 5 min 18 s end to end. Three of the four areas produced six candidates each; `Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations` produced none. Referee A scored all 18 candidates live and six were published.

| | Baseline (7 default-walk results) | Whole pool (18) | Published (6) |
|---|---|---|---|
| Referee A expected score, mean | 2.58 | 3.84 | 4.54 |
| Referee A expected score, range | 1.40 to 4.46 | 2.72 to 5.72 | 3.52 to 5.72 |
| Referee A importance, mean | 2.43 | | 4.67 |
| P(surprising), mean | 0.10 | | 0.26 |
| P(a human cares), mean | 0.10 | | 0.28 |
| Referee B importance, mean | 1.14 | | 1.00 |

The published column is selected by Referee A's own score, so the whole-pool column is the fair comparison for the generator: every candidate in the pool scored above the baseline mean, and four scored above the baseline maximum. Selection from the pool adds a further 0.70. Both samples are small, and the baseline results came from the default walk.

Referee B gave all six results a 1, so the second success criterion is unmet. Its justifications no longer describe padding or redundant terms. They make a different objection, the same one six times: the conclusion is an elementary fact that holds in far greater generality, and the domain-specific setting and some hypotheses are superfluous. Examples: a closed map has a closed range, which is stable under specialization, with schemes and injectivity playing no part; a proper subset has a nonempty complement, with the preorder playing no part. The candidate log agrees with this reading: in 14 of the 18 candidates the seed is the only step whose lemma is defined under the focus.

The interest score does not predict Referee A on this pool. The rank correlation is -0.29 (n = 18), and the two highest-rated candidates have strongly negative interest scores, because the size penalty is taken on the fully explicit statement, which is very large for scheme statements. Steps (-0.46) and distinct concepts (-0.36) correlate negatively as well. With 18 candidates from three modules this is a warning and no more, since module and statement size are confounded. It matters because the same score orders the kept derivations inside a walk and ranks the pool offline.

What this suggests for the next iteration, in order: require more than one on-topic step, or a conclusion that fails once the focus-specific hypotheses are dropped; take the size penalty on the readable statement; refit the interest score against `state/candidates.jsonl` once a week of nightly runs has filled it.

### Follow-up after the live run

Two of the three suggestions were built; the third needs a week of nightly data.

**Size penalty on the readable statement.** `interest.readable_size` is the statement's `visibleSize` (explicit arguments and explicit hypotheses), and the score subtracts a tenth of it. `interest.statement_size` is still reported and no longer enters the score. On the benchmark and the replayed live modules the readable size ranges from 20 to 74 while the explicit count ranges from 141 to 1333, so the penalty is now between 2 and 7 points for every module. The divisor of 10 is a guess: a 60-symbol statement costs as much as two concepts earn.

**On-topic floor.** `--min-focus-steps` sets how many retained steps must use a lemma defined under the focus; the seed is one of them. While a derivation is short of the floor, three extensions out of four draw from focus lemmas when the matching pool has any. Measured before choosing a default:

| | Floor 1 | Floor 2, no steering | Floor 2, with steering |
|---|---|---|---|
| Benchmark candidates (modules) | 11 (3) | 9 (2) | 9 (2) |
| Live-run modules replayed offline: graph walks | 6 | 4 | 5 |
| Live-run modules replayed offline: upper and lower sets | 6 | 1 | 5 |
| Live-run modules replayed offline: schemes | 6 in the live run | 0 | 0 |

The replay used the live run's seed and profiles, asking for six candidates per module. The scheme module timed out locally at floor 1 while three walks ran at once, so its floor 1 figure is the live run's.

A floor of 2 therefore costs about half of the pool. `Mathlib.RingTheory.Localization.Ideal` and `Mathlib.AlgebraicGeometry.Scheme` yield nothing under it; the first has few indexed focus lemmas because most of its statements are equivalences, which the index leaves out. The scheme module produced the two results Referee A rated highest in the live run, each with the seed as its only on-topic step. Read by eye, the statements that survive the floor stay in the vocabulary of their area and still wander through generic lattice facts, so the floor is not shown to answer Referee B.

For that reason the floor is a setting with default 1, and `wander.py` gives each explored module a floor of 1 or 2 at random. `state/wander.json` records the floor of every explored module next to its referee scores, and `state/candidates.jsonl` records `focus_steps` for every screened candidate, so a week of nightly runs compares the two settings on live referees. Making 2 the rule is a one-line change in `_mutate_knobs`.

Benchmark after the follow-up, default settings (`bench/followup.json`): 142.2 s wall, 92.0 s search, 11 candidates, 11 valid, 3 modules, 0 violations. With `--min-focus-steps 2` (`bench/followup-floor2.json`): 125.7 s wall, 84.5 s search, 9 valid, 2 modules, 0 violations. Search time at default settings is 15 s above the `final` row; whether that is the readable-size computation or variation between runs was not isolated.

Still open: refitting the interest score against the candidate log, and indexing equivalences (as two implications) so that modules made mostly of `iff` statements can supply on-topic steps.

### First nightly run on `main`

Manual run of the nightly workflow on `main` after the merge (2026-11-25, Actions run 45519007453, results `AKCM-2026-0008` to `AKCM-2026-0013`, bot commit `022dc50`). Four modules were explored, 15 candidates screened, six published.

| | Baseline (7 results) | Feature-branch run | This run |
|---|---|---|---|
| Referee A expected score, published, mean | 2.58 | 4.54 | 4.34 |
| Referee A expected score, whole pool, mean | not screened | 3.84 (18) | 3.91 (15) |
| Referee B importance, published, mean | 1.14 | 1.00 | 1.17 |

The gain with Referee A holds on four modules that the feature-branch run did not visit. Referee B is where it was: five results at 1 and one at 2.

Three of the four modules drew an on-topic floor of 2, and one of those three (`Mathlib.AlgebraicTopology.SimplicialObject.Split`) yielded nothing. Candidates from floor-2 modules average 3.91 with Referee A (9 candidates) and candidates from the floor-1 module average 3.91 (6 candidates). By candidate, those whose only on-topic step is the seed average 4.16 (4 candidates) and the others 3.82 (11 candidates). One run with different modules in each group settles nothing, and what it shows does not favour the floor.

Referee B's reasons are now specific. In four of the six reports it names hypotheses that do no work: a hypothesis about a variable that occurs nowhere else in the statement (`PowerSeries.HasEval a` in `AKCM-2026-0008`), hypotheses that are unnecessary because the fibre of a bijection over a point is a singleton (`AKCM-2026-0012` and `AKCM-2026-0013`), and a field-extension setting around a divisibility fact about natural numbers (`AKCM-2026-0011`).

### Hypotheses that do no work, and a broken gate

Work prompted by Referee B's reports on the first nightly run.

**Dangling hypotheses.** Specialist search now drops a closed statement in which some hypothesis shares no variable with the conclusion, directly or through other hypotheses. Occurrences are counted as a reader sees them (explicit arguments). This matters for the case that prompted the check: in `AKCM-2026-0008` the variable `a` of `PowerSeries.HasEval a` does occur a second time, inside an unprinted topology argument of another hypothesis, so a check on raw occurrences finds nothing. That statement has a second defect the check does not address: one of its hypotheses is stated for a non-standard topology, which the printed form hides.

**The `exact?` gate never worked on statements with hypotheses.** `librarySearch` was called outside the goal's local context and threw on the first introduced hypothesis; the catch around the gate read the error as "not closed". The defect predates this work. With the search run inside the goal's context, a statement that is exactly `Set.Subset.trans` is closed, with or without an extra hypothesis (test in `Babel/Tests.lean`). A failure of a gate that is not a spent budget is now counted as `gate_error`.

Checked against what was published: of the twelve results from the two live runs, a working `exact?` over all of Mathlib closes one, `AKCM-2026-0012`, the result Referee B called a tautology. The seven older results were not checked.

**The drop-one-hypothesis gate was not built.** The idea was to reject a statement that automation still proves after one hypothesis is removed. On the twelve published statements, `simp_all`, `aesop` and `grind` close none of the reduced statements, and `exact?` closes only reduced forms of `AKCM-2026-0012`, which the repaired gate rejects whole. The gate would have added tactic calls per hypothesis and caught nothing new.

Benchmark with both changes (`bench/gates.json`): 10 candidates, 10 valid, 2 modules, 0 violations; one statement rejected by `exact?` (the only candidate of the short exact sequence module, which was one lemma away), two derivations rejected for a dangling hypothesis, no gate errors. The run took 271 s of wall time on a machine that was swapping; phase timings show index building and tree building slowed by the same factor as the search, and the two new computations took about 10 ms per run.


### Referee calibration on real Mathlib theorems

Both referees scored 50 Mathlib theorems through the production prompt (2026-11-25, Actions run 45547148937, scores in `bench/calibration-2026-11-25.json`): 18 named theorems and 8 trivial facts chosen by hand, and a seeded random sample of 24 theorems from the eight modules the search has explored or is benchmarked on. The 13 published results were scored again in the same run. Referee A was asked once per item and Referee B three times; 187 of Referee B's 189 calls returned a score.

| Tier | Items | Referee A mean | Referee B mean | Referee B lowest and highest item | Referee B noise SD |
|---|---|---|---|---|---|
| Named theorems | 18 | 7.13 | 4.94 | 1.33 to 8.67 | 1.40 |
| Random library theorems | 24 | 4.27 | 1.68 | 0.33 to 3.67 | 0.41 |
| Trivial facts | 8 | 1.28 | 0.04 | 0.00 to 0.33 | 0.20 |
| Published results | 13 | 3.60 | 1.18 | 1.00 to 2.00 | 0.23 |

Referee B's score for an item is the mean of its repeats. The noise SD is the pooled standard deviation of the repeats on one item.

**Both referees use their scale.** Referee B gives the trivial facts a 0 in 23 of 24 calls, the fundamental theorem of algebra a 9 in two of three, and the average library theorem between 1 and 2. Over the 50 Mathlib items the two referees rank alike (rank correlation 0.92). Referee A separates the hand-picked tiers completely: its highest trivial fact scores 1.91 and its lowest named theorem 6.17.

**A score of 1 from Referee B is a stable verdict.** On 11 of the 13 published results every repeat equals the stored score, and the standard deviation of the repeats on one result is 0.23. Referee A returns the same expected score for the six results of the first nightly run to three decimals. The seven older results score differently today because their records were read in a different form when they were first scored.

**Where the published results stand.** With Referee B they are at 1.18, below the average random library theorem (1.68) and at the level of the library's boilerplate: 10 of the 24 sampled theorems score 1 or less. With Referee A the six results of the first nightly run average 4.34, which is the level of the average library theorem (4.27), and the best of them scores above 17 of the 24. On real theorems the two referees agree; on generated ones Referee A places the result in the middle of the library and Referee B at the bottom. Referee B's reports say why: hypotheses that do no work and a subject that is decoration. Referee A does not see either.

**What is within reach.** Three of the 24 sampled theorems reach a Referee B mean of 3 and none reaches 4; half reach 2. A mechanically derived statement that Referee B rated like a good library theorem would score 2 to 3. Higher scores went only to theorems the referee recognises by name.

**Referee B reads the lemma list.** Named theorems that Mathlib proves in one or two steps from a stronger lemma score low: the irrationality of the square root of two 1.33 ("a two-step specialization of `Nat.Prime.irrational_sqrt`"), the mean value theorem 2.00, rank and nullity 2.67. Among the named theorems, Referee B's score follows the ratio of proof size to statement size (rank correlation 0.86), and among the library sample it follows the number of cited lemmas (0.84). Both are observations on small samples in which deeper theorems also have longer proofs, so they do not show that a longer list raises a score.

**Equivalences score somewhat higher.** In the library sample, the ten equivalences average 2.03 with Referee B, the four generated projection equations 1.25, and the ten others 1.50. The generator never produces an equivalence, since the lemma index leaves them out.

Limits of the comparison: every Mathlib theorem was shown with the badges of a published result ("`exact?` failed", "not routine"), which is false for the trivial facts; the lemma list and size ratio come from the real proof and are not inflated as the journal's are; and the prompt tells the referee that the journal publishes unimportant theorems, which did not stop it from giving a 9.

The run also exposed a defect. Two of Referee B's replies were not valid JSON (a backslash escape inside a string), and `extract_json` raised an error that `process_editorial` does not catch, so the same reply during a nightly run would have ended the run after verification. `extract_json` now raises `LLMError`, which the editorial desk handles by falling back.

### Decoration and shortcuts, measured on the published derivations

Two candidate gates were measured offline on the twelve specialist results of the two live runs, each with the imports of its own module, which is what a gate sees during a walk. The harness was scratch code and is not in the repository.

**Decoration test: 0 of 12.** The idea was to replace every maximal term whose head is defined under the focus by a variable and to reject the candidate when automation proves the generic statement. Nine of the twelve statements have a well-typed generic form, and `exact?`, `simp`, `aesop` and `grind` prove none of them; for the other three the generic form does not type-check. The generic forms are often true (the scheme result becomes a statement about any morphism of locally ringed spaces), and proving them takes two lemmas or more. The test was not built.

**Shortcut check: 6 of 12, of which 5 are defects of the statement.** For every fact a derivation reaches in two or more lemma steps, ask the Level 1 question: do the theorem's hypotheses give it by assumption, reflexivity or one library lemma? Steps spent on a proof that occurs inside the fact's own statement are not counted. Where a shortcut exists, substituting it into the proof shows what the detour was carrying.

| Result | Shortcut | Hypotheses no longer used | Focus lemmas | Lemma steps |
|---|---|---|---|---|
| Schemes, feature-branch `0008` | "f is a closed map" is derived in 3 steps and is a hypothesis | injectivity of f | 1 to 0 | 5 to 2 |
| Upper sets, feature-branch `0011` | a strict inclusion derived in 7 steps is a hypothesis | `IsUpperSet s` | 2 to 0 | 9 to 2 |
| Upper sets, feature-branch `0013` | an inclusion derived in 2 steps is a hypothesis up to unfolding | none | 1 to 0 | 10 to 8 |
| Constant functions, `AKCM-2026-0012` | the conclusion itself (the existing gate) | both | 2 to 1 | 6 to 2 |
| Constant functions, `AKCM-2026-0013` | a fact derived in 6 steps needs no hypothesis | bijectivity of f, constancy of u | 3 to 2 | 7 to 3 |
| Graphs, feature-branch `0010` | a fact derived in 5 steps is a library lemma | none | 1 to 1 | 10 to 6 |

In the first five the shortcut removes a hypothesis or every focus lemma, and in each case this is what Referee B objected to in its report ("the hypothesis of injectivity, as well as the entire scheme-theoretic apparatus, is entirely superfluous"). The sixth is a detour in the proof that leaves the statement as it was.

The six results without a shortcut all scored 1 with Referee B as well. One has a dangling hypothesis, which is now rejected. The other five are a focus fact followed by generic steps (an inequality of fixed fields fed into order theory, an index identity fed into divisibility), and no check measured so far separates them from a good statement. A shortcut gate would remove the clearest defects; it should not be expected to raise Referee B's score on what remains.

**The shortcut gate was built** as the last gate of specialist search (`hasDefectiveShortcut` in `Babel/Gate.lean`). It rejects a derivation when a shortcut exists and the shorter proof no longer uses some hypothesis or no longer uses any focus lemma; a detour that only lengthens the proof is tolerated, which lets the graph result of the table above pass. Benchmark (`bench/shortcut.json`): 10 candidates, 10 valid, 2 modules, 0 violations, the same yield as before, with one derivation rejected by the new gate and no gate errors. The gate is the most expensive one: it took 42 s of a 60 s run on the filter module, about 8 s per candidate that reaches it, because every intermediate fact without a shortcut costs a full library search.

### A timed launch on a clean slate

The launch issue is generated differently from a nightly batch. Generation runs in rounds over fresh modules until a time budget is spent, since a single round finishes in minutes whatever limit the job is given. The pooled candidates are cut to a shortlist by the interest score, within modules only: the score had a rank correlation of -0.29 with Referee A on the first pool, so it is trusted to order one module's candidates and not to compare modules. Referee A ranks the shortlist, and Referee B scores the top of that ranking as well; the mean of the two decides the order of verification. The calibration run is the reason for bringing Referee B in: on real theorems the two referees agree, and on generated ones only Referee B sees unused hypotheses and decorative subjects. A result selected this way carries a Referee B score that was selected for, which the record notes (`selection.second_opinion`).

The thirteen results published before this were removed, and the issue and family state reset, so that the launch issue is the journal's first content. Three of the six most recent ones fail a gate built since they were published.
