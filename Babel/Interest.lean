import Lean
import Babel.Util

namespace Babel

open Lean Meta

/-- Limits applied to every lemma application during a walk. -/
structure StepLimits where
  /-- How often one lemma may occur among the ancestors of a step. -/
  maxLemmaRepeats : Nat := 1
  /-- Expression-node cap on a derived fact's statement. -/
  maxFactSize : Nat := 400
  /-- Heartbeat budget (in thousands) for the padded-fact check. -/
  simpBudget : Nat := 20000
deriving Inhabited

/-- What the cheap interest score is computed from. -/
structure InterestComponents where
  /-- Distinct head predicates among the retained steps. -/
  concepts : Nat := 0
  /-- Distinct defining modules among the retained lemmas. -/
  modules : Nat := 0
  /-- Retained derivation steps. -/
  steps : Nat := 0
  /-- Steps that combine two independent branches. -/
  joins : Nat := 0
  /-- Expression nodes in the closed statement. -/
  statementSize : Nat := 0
deriving Inhabited, Repr

/-- A cheap proxy for how interesting a derivation is: it rewards passing through
    distinct concepts and modules with a long derivation, and penalises a large statement.
    The weights are defaults to be compared with referee scores, not tuned values. -/
def interestScore (c : InterestComponents) : Float :=
  3.0 * c.concepts.toFloat + 2.0 * c.modules.toFloat + c.steps.toFloat
    + (if c.joins > 0 then 2.0 else 0.0) - c.statementSize.toFloat / 40.0

/-- The concept a fact is about: the head constant of its statement. -/
def conceptOf (factType : Expr) : Option Name :=
  factType.getAppFn.constName?

def countDistinct (names : Array (Option Name)) : Nat :=
  let distinct := names.foldl (init := (#[] : Array Name)) fun acc name? =>
    match name? with
    | some name => if acc.contains name then acc else acc.push name
    | none => acc
  distinct.size

/-- The default `simp` set with its simprocs, as the `simp` tactic would use. -/
def defaultSimpContext : MetaM (Simp.Context × Simp.SimprocsArray) := do
  return (← Simp.Context.mkDefault, #[← Simp.getSimprocs])

/-- Simplify a statement with the default simp set. `none` on timeout or failure. -/
def simplifiedSize? (e : Expr) (budget : Nat) : MetaM (Option (Expr × Nat)) := do
  let saved ← saveState
  try
    tryCatchRuntimeEx
      (withHeartbeatBudget budget do
        let (ctx, simprocs) ← defaultSimpContext
        let (result, _) ← Meta.simp e ctx simprocs
        let simplified ← instantiateMVars result.expr
        return some (simplified, exprSize simplified))
      (fun _ => pure none)
  finally
    restoreState saved

/-- A fact is padded when `simp` proves it outright or rewrites it to something smaller:
    the statement then carries terms that add nothing, such as `s ∩ s`. -/
def isPaddedFact (e : Expr) (budget : Nat := 20000) : MetaM Bool := do
  match ← simplifiedSize? e budget with
  | none => return false
  | some (simplified, size) => return simplified.isConstOf ``True || size < exprSize e

end Babel
