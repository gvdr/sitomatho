import Babel.Stats
import Babel.Interest
import Babel.Generator
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic

/-!
Build-time checks for the pure parts of the generator.
Run with `lake build BabelTest`; a failing `#guard` fails the build.
-/

open Babel

#guard (({} : WalkStats).bump .selfReuse |>.bump .selfReuse).rejects.getD "self_reuse" 0 == 2
#guard (({} : WalkStats).addMs "search" 40 |>.addMs "search" 2).phaseMs.getD "search" 0 == 42
#guard (({} : WalkStats).bump .closedByExact |>.bump .paddedFact |>.bump .paddedFact).dominantReject
  == some ("padded_fact", 2)
#guard ({} : WalkStats).dominantReject == none

/-! ## Interest score and padded facts -/

section Interest

open Lean Meta Elab Term

#guard interestScore { concepts := 3, modules := 2, steps := 5, joins := 1, readableSize := 20 } == 15.0
-- Staying on the subject is rewarded more than touching one more module.
#guard interestScore { concepts := 3, modules := 2, steps := 5, focusSteps := 4 } >
       interestScore { concepts := 3, modules := 5, steps := 5, focusSteps := 1 }
#guard interestScore { concepts := 4, modules := 2, steps := 5, joins := 0, readableSize := 20 } >
       interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, readableSize := 20 }
#guard interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, readableSize := 100 } <
       interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, readableSize := 20 }
-- The penalty is on what a reader sees: instance arguments, which make scheme statements
-- thousands of nodes long, do not lower the score.
#guard interestScore { concepts := 3, steps := 5, statementSize := 8000, readableSize := 20 } ==
       interestScore { concepts := 3, steps := 5, statementSize := 100, readableSize := 20 }
#guard countDistinct #[some `A, none, some `B, some `A] == 2

/-- Elaborate a closed term from source text. Parsing a string avoids the hygienic binder
    names a syntax quotation would introduce. -/
def elabClosed (source : String) (expectedType? : Option Expr := none) : TermElabM Expr := do
  match Parser.runParserCategory (← getEnv) `term source with
  | .error message => throwError message
  | .ok stx =>
      let e ← elabTerm stx expectedType?
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e

/-- Apply `k` to the body of a closed `∀` statement. -/
def onBody (source : String) (k : Expr → MetaM Bool) : TermElabM Bool := do
  forallTelescope (← elabClosed source) fun _ body => k body

/-- info: true -/
#guard_msgs in
#eval onBody "∀ (α : Type) (s t : Set α), s ∩ s ⊆ t" (isPaddedFact ·)

/-- info: false -/
#guard_msgs in
#eval onBody "∀ (α : Type) (s t : Set α), s ⊆ t" (isPaddedFact ·)

/-- Padding inside an argument counts even when `simp` rewrites the whole statement into a
    larger unfolded form. -/
def paddedArgument : TermElabM Bool :=
  onBody "∀ (α : Type) (s t : Set α) (l : Filter α), (s ∩ t)ᶜᶜ ≤ᶠ[l] tᶜᶜ" (isPaddedFact ·)

/-- info: true -/
#guard_msgs in
#eval paddedArgument

/-- info: false -/
#guard_msgs in
#eval onBody "∀ (α : Type) (s t : Set α) (l : Filter α), s ≤ᶠ[l] t" (isPaddedFact ·)

/-- A set written as `fun x ↦ x ∈ s` is the set itself in unfolded form. -/
def etaExpandedSet : TermElabM Bool :=
  onBody "∀ (α : Type) (s t : Set α) (l : Filter α), (fun x => x ∈ s) ≤ᶠ[l] fun x => x ∈ t"
    (isPaddedFact ·)

/-- info: true -/
#guard_msgs in
#eval etaExpandedSet

/-- Padding found by the final review. Sizes must be compared as a reader sees them:
    `simp` removes `ᶜᶜ` but elaborates longer instance paths, so a node count that includes
    instance arguments calls the simplified term larger. -/
def reviewPaddingCases : TermElabM (List Bool) := do
  return [
    ← onBody "∀ (α : Type) (s t : Set α) (l : Filter α), (s ∩ t)ᶜᶜ ≤ᶠ[l] t" (isPaddedFact ·),
    ← onBody "∀ (α β : Type) (f : α → β) (u : Set β) (v : Set α) (w : Filter α), ((f ⁻¹' u)ᶜ ∩ v)ᶜᶜ ≤ᶠ[w] vᶜ ∩ f ⁻¹' u"
        (isPaddedFact ·),
    ← onBody "∀ (α : Type) (s t : Set α) (l : Filter α), ∃ v ∈ l, ∀ y ∈ v, y ∈ sᶜ ∪ s ↔ y ∈ tᶜ ∪ t"
        (isPaddedFact ·),
    ← onBody "∀ (α β : Type) (f : α → β) (u : Set β) (v : Set α) (w : Filter α), (f ⁻¹' u)ᶜ ∩ v ≤ᶠ[w] vᶜ ∩ f ⁻¹' u"
        (isPaddedFact ·)]

/-- info: [true, true, true, false] -/
#guard_msgs in
#eval reviewPaddingCases

-- A short derivation through many concepts outranks a long chain of on-topic closure lemmas.
#guard interestScore { concepts := 5, modules := 4, steps := 5, focusSteps := 2 } >
       interestScore { concepts := 3, modules := 1, steps := 12, focusSteps := 12 }

end Interest

/-! ## Step-level checks -/

#guard ancestorLemmas
  #[{ (default : WalkStep) with stepIdx := 0, lemmaName := `A, parentSteps := #[] },
    { (default : WalkStep) with stepIdx := 1, lemmaName := `B, parentSteps := #[0] },
    { (default : WalkStep) with stepIdx := 2, lemmaName := `C, parentSteps := #[] }]
  #[1] == #[`B, `A]

/-- A two-premise lemma applied to one fact must be able to assume its other premise:
    here `Set.Subset.trans` on `s ⊆ t` introduces a new set `c` and the hypothesis `t ⊆ c`. -/
def opensNewHypothesis : Lean.Elab.Term.TermElabM Bool := do
  let stmt ← elabClosed "∀ (α : Type) (s t : Set α), s ⊆ t → True"
  Lean.Meta.forallBoundedTelescope stmt (some 4) fun xs _ => do
    let h := xs[3]!
    let target : WalkStep := {
      stepIdx := 0, lemmaName := `seed, namespaceName := "Set"
      factType := ← Lean.Meta.inferType h, factProof := h, parentSteps := #[] }
    let stats ← IO.mkRef {}
    let (result, _) ← tryApplyLemma stats {} ``Set.Subset.trans target #[target] xs 0 1 (Rng.ofSeed 1)
    let some (specs, mkStep) := result | return false
    let opened ← withOpenedBinders stats specs.toList #[] fun fresh => do
      let some step ← mkStep fresh | return none
      return some (fresh.size, step.factType.getAppNumArgs, step.parentSteps)
    return opened == some (2, 4, #[0])

/-- info: true -/
#guard_msgs in
#eval opensNewHypothesis

-- Two branches that each used a lemma once must not be joined past the repetition cap.
#guard exceedsRepeatCap #[`A, `B, `A] 1
#guard !exceedsRepeatCap #[`A, `B] 1
#guard !exceedsRepeatCap #[`A, `A] 2

namespace Tests

theorem familyLemma {α : Type} {β : α → Type} {s t : Set α} (h : s ⊆ t)
    (_f : (x : α) → β x → Prop) : s ⊆ t := h

theorem trivialPremise {α : Type} {s t : Set α} (h : s ⊆ t) (_h2 : ¬False) : s ⊆ t := h

theorem falsePremise {α : Type} {s t : Set α} (h : s ⊆ t) (_h2 : (1 : Nat) = 2) : s ⊆ t := h

end Tests

/-- Whether applying `lemmaName` to the fact `s ⊆ t` gets as far as opening its new binders. -/
def opensBindersFor (lemmaName : Lean.Name) : Lean.Elab.Term.TermElabM Bool := do
  let stmt ← elabClosed "∀ (α : Type) (s t : Set α), s ⊆ t → True"
  Lean.Meta.forallBoundedTelescope stmt (some 4) fun xs _ => do
    let h := xs[3]!
    let target : WalkStep := {
      stepIdx := 0, lemmaName := `seed, namespaceName := "Set"
      factType := ← Lean.Meta.inferType h, factProof := h, parentSteps := #[] }
    let stats ← IO.mkRef {}
    let (result, _) ← tryApplyLemma stats {} lemmaName target #[target] xs 0 1 (Rng.ofSeed 1)
    let some (specs, _) := result | return false
    return (← withOpenedBinders stats specs.toList #[] fun _ => pure (some ())).isSome

/-- info: (true, false, false, false) -/
#guard_msgs in
#eval do
  return (← opensBindersFor ``Set.Subset.trans, ← opensBindersFor ``Tests.familyLemma,
    ← opensBindersFor ``Tests.trivialPremise, ← opensBindersFor ``Tests.falsePremise)

/-! ## Kept derivations -/

private def kd (hash : String) (score : Float) : KeptDerivation :=
  { (default : KeptDerivation) with stmtHash := hash, score := score }

#guard (insertKept (insertKept (insertKept #[] (kd "a" 1.0) 2) (kd "b" 3.0) 2) (kd "c" 2.0) 2).map (·.stmtHash)
  == #["b", "c"]
#guard (insertKept (insertKept #[] (kd "a" 1.0) 3) (kd "a" 9.0) 3).size == 1
#guard (insertKept (insertKept #[] (kd "a" 2.0) 3) (kd "b" 2.0) 3).map (·.stmtHash) == #["a", "b"]

/-- A conclusion that is itself a `∀` must stay in the conclusion: exactly the recorded
    number of binders is opened as hypotheses. -/
def renderForallConclusion : Lean.Elab.Term.TermElabM Bool := do
  let stmt ← elabClosed "∀ (α : Type) (s : Set α), s ⊆ s → ∀ x ∈ s, x ∈ s"
  let proof ← elabClosed "fun (α : Type) (s : Set α) (h : s ⊆ s) => fun x hx => h hx" (some stmt)
  let some (decl, _, _) ← renderStandaloneClosed "akcm_candidate" stmt proof 3 #[] 0 0
    | return false
  return (decl.splitOn "(h_3 : s ⊆ s)").length == 2 && (decl.splitOn "∀ x ∈ s, x ∈ s").length == 2

/-- info: true -/
#guard_msgs in
#eval renderForallConclusion

/-- Lemmas stated purely in logical and basic order vocabulary are glue, not mathematics. -/
def glueLemmas : Lean.Meta.MetaM (List Bool) := do
  let env ← Lean.getEnv
  return [isGlueLemma env ``ne_of_eq_of_ne, isGlueLemma env ``mt, isGlueLemma env ``not_or_intro,
    isGlueLemma env ``Set.mem_of_eq_of_mem, isGlueLemma env ``Set.inter_subset_left,
    isGlueLemma env ``Filter.inter_mem]

/-- info: [true, true, true, true, true, false] -/
#guard_msgs in
#eval glueLemmas

/-- Deprecated aliases and auto-generated lemmas stay out of the index: an alias would let
    one lemma be applied twice under two names. -/
def indexHygiene : Lean.Meta.MetaM (List Bool) := do
  let index := buildLemmaIndex (← Lean.getEnv)
  return [index.conclHead.contains ``Filter.EventuallySubset.compl,
    index.conclHead.contains ``Filter.EventuallyLE.compl,
    isCleanMathlibName `IsLocalization.mk'.congr_simp,
    isCleanMathlibName `CategoryTheory.ShortComplex.HomotopyEquiv.mk.injEq]

/-- info: [true, false, false, false] -/
#guard_msgs in
#eval indexHygiene

/-! ## On-topic steps -/

#guard Reject.fewFocusSteps.key == "few_focus_steps"

-- With a floor of two, the seed alone does not make a derivation on-topic: a second step
-- must use a focus lemma. The default floor of one is met by the seed.
#guard specialistShortfall { focus := `Mathlib.Order, minFocusSteps := 2 } 5 4 1 == some .fewFocusSteps
#guard specialistShortfall { focus := `Mathlib.Order, minFocusSteps := 2 } 5 4 2 == none
#guard specialistShortfall { focus := `Mathlib.Order, minFocusSteps := 2 } 3 4 3 == some .fewSteps
#guard specialistShortfall { focus := `Mathlib.Order, minFocusSteps := 2 } 5 2 3 == some .fewConcepts
#guard specialistShortfall { focus := `Mathlib.Order } 5 4 1 == none

-- Lemmas of the focus area are preferred when the pool has any, and the pool is kept otherwise.
#guard preferFocus #[`A, `B, `C] (fun n => n == `B || n == `C) == #[`B, `C]
#guard preferFocus #[`A, `B] (fun _ => false) == #[`A, `B]

/-! ## Hypotheses unrelated to the conclusion -/

section Dangling

open Lean Meta Elab Term

/-- A predicate with an implicit argument a reader never sees. -/
def tagged {α : Type} {_witness : α} (s : Set α) : Prop := s.Nonempty

/-- Indices of the dangling hypotheses among the first `nBinders` binders of a statement. -/
def dangling (source : String) (nBinders : Nat) : TermElabM (Array Nat) := do
  danglingHypotheses (← elabClosed source) nBinders

/-- `u ⊆ u` is about a set that appears nowhere else in the statement. -/
def danglingCases : TermElabM (List (Array Nat)) := do
  return [
    ← dangling "∀ (α : Type) (s t u : Set α), s ⊆ t → u ⊆ u → s ∩ t = s" 6,
    -- Reached through a chain: `t ⊆ u` shares `t` with `s ⊆ t`, which shares `s` with the conclusion.
    ← dangling "∀ (α : Type) (s t u : Set α), s ⊆ t → t ⊆ u → s ∩ s = s" 6,
    -- Only the recorded binders are hypotheses: the conclusion here is itself a `∀`.
    ← dangling "∀ (α : Type) (s : Set α), s.Nonempty → ∀ t : Set α, s ⊆ t → t.Nonempty" 3,
    -- Reached through the type of a variable: `x : ↥s` ties `s` to the conclusion.
    ← dangling "∀ (α : Type) (s : Set α) (x : ↥s) (y : α), y ∈ s → x = x" 5,
    -- A hypothesis about the ambient type alone is not judged.
    ← dangling "∀ (α : Type) (s : Set α), Nonempty α → s ⊆ s" 3,
    -- Two hypotheses about each other and about nothing in the conclusion.
    ← dangling "∀ (α : Type) (s t u v : Set α), u ⊆ v → v ⊆ u → s ⊆ s ∪ t" 7,
    -- Occurrences are counted as a reader sees them: `a` also occurs in an implicit
    -- argument of `tagged s`, which is not printed, so `a = a` still dangles.
    ← dangling "∀ (α : Type) (a : α) (s : Set α), a = a → @tagged α a s → s.Nonempty" 5]

/-- info: [#[5], #[], #[], #[], #[], #[5, 6], #[3]] -/
#guard_msgs in
#eval danglingCases

end Dangling

#guard Reject.danglingHypothesis.key == "dangling_hypothesis"

/-! ## The `exact?` gate -/

section ExactGate

open Lean Meta Elab Term

/-- A statement that is one library lemma away must be closed by the Level 1 gate at the
    budget the pipeline uses, with or without an extra hypothesis in the context. -/
def exactGateCases : TermElabM (List Bool) := do
  return [
    ← Babel.closedByExact? (← elabClosed "∀ (α : Type) (s t u : Set α), s ⊆ t → t ⊆ u → s ⊆ u") 150000,
    ← Babel.closedByExact? (← elabClosed "∀ (α : Type) (s t u : Set α), s.Nonempty → s ⊆ t → t ⊆ u → s ⊆ u") 150000,
    ← Babel.closedByExact? (← elabClosed "∀ (α : Type) (s t : Set α), s ⊆ t → t ⊆ s") 150000]

/-- info: [true, true, false] -/
#guard_msgs in
#eval exactGateCases

end ExactGate

/-! ## Gate errors are counted -/

/-- A gate that throws is reported as "not closed", which is how the `exact?` gate stayed
    broken unnoticed. The failure must at least be counted. -/
def gateErrorIsCounted : Lean.Meta.MetaM (Bool × Nat) := do
  let stats ← IO.mkRef ({} : WalkStats)
  let closed ← tryWithHeartbeats 1000 (throwError "boom") (some stats)
  return (closed, (← stats.get).rejects.getD "gate_error" 0)

/-- info: (false, 1) -/
#guard_msgs in
#eval gateErrorIsCounted

/-- Each Level 2 gate closes a statement it should close, leaves an unprovable one open, and
    an ordinary failure to prove ("made no progress") is not counted as a gate error. -/
def levelTwoGateCases : Lean.Elab.Term.TermElabM (List Bool × Nat) := do
  let stats ← IO.mkRef ({} : WalkStats)
  let easy ← elabClosed "∀ (α : Type) (s t u : Set α), s ⊆ t → s ∩ u ⊆ t ∪ u"
  let open_ ← elabClosed "∀ (α : Type) (s t : Set α), s ⊆ t → t ⊆ s"
  let results := [
    ← closedBySimp (← elabClosed "∀ (α : Type) (s : Set α), s ∩ s = s") 150000 (some stats),
    ← closedBySimp open_ 150000 (some stats),
    ← closedByAesop easy 150000 (some stats),
    ← closedByAesop open_ 150000 (some stats),
    ← closedByExact? open_ 150000 (some stats)]
  return (results, (← stats.get).rejects.getD "gate_error" 0)

/-- info: ([true, false, true, false, false], 0) -/
#guard_msgs in
#eval levelTwoGateCases
