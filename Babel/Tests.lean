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

#guard interestScore { concepts := 3, modules := 2, steps := 5, joins := 1, statementSize := 80 } == 15.0
-- Staying on the subject is rewarded more than touching one more module.
#guard interestScore { concepts := 3, modules := 2, steps := 5, focusSteps := 4 } >
       interestScore { concepts := 3, modules := 5, steps := 5, focusSteps := 1 }
#guard interestScore { concepts := 4, modules := 2, steps := 5, joins := 0, statementSize := 80 } >
       interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, statementSize := 80 }
#guard interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, statementSize := 400 } <
       interestScore { concepts := 3, modules := 2, steps := 5, joins := 0, statementSize := 80 }
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
