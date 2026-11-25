import Lean
import Lean.Meta.Tactic.LibrarySearch
import Aesop
import Babel.Util
import Babel.Stats
import Babel.Interest

namespace Babel

open Lean Meta

structure NoveltyReport where
  level0Unseen : Bool := true
  level1ExactFailed : Bool
  level1BudgetHeartbeats : Nat
  level2NotRoutine : Bool
  level2ClosedBy : Option String
  level3ProofSize : Nat
  level3StatementSize : Nat
  level3Ratio : Float
deriving Inhabited

/-- Run a MetaM action with an isolated heartbeat budget. Running out of budget and any
    other failure both answer `false`; a failure that is not a spent budget is counted as
    `gate_error`, since a gate that always throws would otherwise pass every statement. -/
def tryWithHeartbeats (budget : Nat) (act : MetaM Bool) (stats : Option StatsRef := none) :
    MetaM Bool := do
  let saved ← saveState
  try
    tryCatchRuntimeEx
      (withHeartbeatBudget budget act)
      (fun e => do
        if !e.isMaxHeartbeat then
          if let some ref := stats then ref.reject .gateError
        pure false)
  finally
    restoreState saved

/-- Level 1 gate: returns `true` iff `exact?` (`librarySearch`) CLOSES the goal. -/
def closedByExact? (stmtType : Expr) (budget : Nat) (stats : Option StatsRef := none) :
    MetaM Bool :=
  tryWithHeartbeats (stats := stats) budget do
    let mvar ← mkFreshExprMVar stmtType
    let (_, goal) ← mvar.mvarId!.intros
    -- First check trivial assumption/rfl
    if (← goal.assumptionCore) then
      return true
    try
      goal.refl
      return true
    catch _ => pure ()
    -- Now run `exact?` (Lean's LibrarySearch). It must run in the goal's local context:
    -- outside it the search throws on the first introduced hypothesis, and the catch
    -- around this gate would report that as "not closed".
    let res ← goal.withContext (Lean.Meta.LibrarySearch.librarySearch goal)
    return res.isNone

/-- Try closing a goal with `simp_all` / `simp`. -/
def closedBySimp (stmtType : Expr) (budget : Nat) (stats : Option StatsRef := none) :
    MetaM Bool :=
  tryWithHeartbeats (stats := stats) budget do
    let mvar ← mkFreshExprMVar stmtType
    let (_, goal) ← mvar.mvarId!.intros
    -- The default simp set and simprocs; an empty context would close almost nothing.
    let (ctx, simprocs) ← defaultSimpContext
    -- `simp` throws when it makes no progress. That is an ordinary "not closed".
    try
      let (res?, _) ← simpGoal goal ctx simprocs (simplifyTarget := true)
      match res? with
      | none => return true
      | some (_, g) =>
          if (← g.assumptionCore) then return true
          g.refl
          return true
    catch _ => return false

/-- Try closing a goal with `aesop`. -/
def closedByAesop (stmtType : Expr) (budget : Nat) (stats : Option StatsRef := none) :
    MetaM Bool :=
  tryWithHeartbeats (stats := stats) budget do
    let mvar ← mkFreshExprMVar stmtType
    let (_, goal) ← mvar.mvarId!.intros
    -- `aesop` throws when it makes no progress. That is an ordinary "not closed".
    try
      let (goals, _) ← Aesop.search goal
      return goals.isEmpty
    catch _ => return false

/-- Evaluate Levels 1, 2, and 3 on a shrunk `(stmtType, proofExpr)` pair. -/
def evaluateNovelty
    (stats : StatsRef)
    (stmtType : Expr)
    (proofExpr : Expr)
    (exactBudget : Nat)
    (aesopBudget : Nat) : MetaM NoveltyReport := do
  let exactClosed ← timed stats "gate_exact" (closedByExact? stmtType exactBudget (some stats))
  let proofSz := exprSize proofExpr
  let stmtSz := exprSize stmtType
  let ratio := Float.ofNat proofSz / Float.ofNat (max 1 stmtSz)

  if exactClosed then
    return {
      level0Unseen := true
      level1ExactFailed := false
      level1BudgetHeartbeats := exactBudget
      level2NotRoutine := false
      level2ClosedBy := some "exact?"
      level3ProofSize := proofSz
      level3StatementSize := stmtSz
      level3Ratio := ratio
    }

  -- Level 2: measure whether routine automation (`simp`, `aesop`) closes it
  let closedBy ←
    if (← timed stats "gate_simp" (closedBySimp stmtType aesopBudget (some stats))) then
      pure (some "simp")
    else if (← timed stats "gate_aesop" (closedByAesop stmtType aesopBudget (some stats))) then
      pure (some "aesop")
    else
      pure none

  return {
    level0Unseen := true
    level1ExactFailed := true
    level1BudgetHeartbeats := exactBudget
    level2NotRoutine := closedBy.isNone
    level2ClosedBy := closedBy
    level3ProofSize := proofSz
    level3StatementSize := stmtSz
    level3Ratio := ratio
  }

end Babel
