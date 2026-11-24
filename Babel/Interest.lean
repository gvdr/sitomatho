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
  /-- New variables and hypotheses a whole derivation may introduce beyond its seed's. -/
  maxNewBinders : Nat := 6
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
  /-- Retained steps whose lemma is defined under the specialist focus. -/
  focusSteps : Nat := 0
deriving Inhabited, Repr

/-- A cheap proxy for how interesting a derivation is. It rewards passing through distinct
    concepts with a long derivation that stays on its subject, and penalises a large
    statement. Distinct modules count for little: weighting them rewarded derivations that
    leave their subject after one step and continue with generic set lemmas.
    The weights are defaults to be compared with referee scores, not tuned values. -/
def interestScore (c : InterestComponents) : Float :=
  3.0 * c.concepts.toFloat + 2.0 * c.focusSteps.toFloat + 0.5 * c.modules.toFloat + c.steps.toFloat
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

/-- A set appearing as a bare predicate: an unapplied `Membership.mem`, or the eta-expanded
    form `fun x ↦ x ∈ s`. Mathlib states some facts about sets through `Set α = α → Prop`,
    and lemmas about functions then produce these forms, which no reader would write. -/
partial def hasUnfoldedSet (e : Expr) : Bool :=
  match e with
  | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      (fn.isConstOf ``Membership.mem && args.size < 5) || hasUnfoldedSet fn || args.any hasUnfoldedSet
  | .lam _ ty body _ =>
      (body.isAppOfArity ``Membership.mem 5 && body.appArg! == .bvar 0 && !body.appFn!.hasLooseBVar 0)
        || hasUnfoldedSet ty || hasUnfoldedSet body
  | .forallE _ ty body _ => hasUnfoldedSet ty || hasUnfoldedSet body
  | .letE _ ty value body _ => hasUnfoldedSet ty || hasUnfoldedSet value || hasUnfoldedSet body
  | .mdata _ inner => hasUnfoldedSet inner
  | .proj _ _ inner => hasUnfoldedSet inner
  | _ => false

/-- The explicit arguments of the head application: the terms a reader sees. -/
def explicitArgs (e : Expr) : MetaM (Array Expr) := do
  let args := e.getAppArgs
  if args.isEmpty then return #[]
  let info ← getFunInfoNArgs e.getAppFn args.size
  let mut explicit := #[]
  for i in [:args.size] do
    if h : i < info.paramInfo.size then
      if info.paramInfo[i].binderInfo == .default then
        explicit := explicit.push args[i]!
  return explicit

/-- A fact is padded when `simp` proves it outright, rewrites it to something smaller, or
    shrinks one of its explicit arguments: the statement then carries terms that add
    nothing, such as `s ∩ s` or `sᶜᶜ`. A set in unfolded form counts as well. The arguments are checked on their own because `simp`
    may also unfold the statement into a larger normal form, which would hide the padding. -/
def isPaddedFact (e : Expr) (budget : Nat := 20000) : MetaM Bool := do
  if hasUnfoldedSet e then
    return true
  if let some (simplified, size) ← simplifiedSize? e budget then
    if simplified.isConstOf ``True || size < exprSize e then
      return true
  for arg in ← explicitArgs e do
    if (← inferType arg).isSort then continue
    if let some (_, size) ← simplifiedSize? arg budget then
      if size < exprSize arg then
        return true
  return false

/-- A hypothesis not worth assuming: `simp` decides it (trivially true, or false and so
    making the theorem vacuous) or it is padded. -/
def isDegenerateHypothesis (e : Expr) (budget : Nat := 20000) : MetaM Bool := do
  if let some (simplified, _) ← simplifiedSize? e budget then
    if simplified.isConstOf ``False then
      return true
  isPaddedFact e budget

end Babel
