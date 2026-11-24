import Babel.Stats
import Babel.Interest
import Mathlib.Data.Set.Basic

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

#guard interestScore { concepts := 3, modules := 2, steps := 5, joins := 1, statementSize := 80 } == 18.0
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

end Interest
