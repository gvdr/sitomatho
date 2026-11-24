import Lean
import Lean.Meta.Tactic.LibrarySearch
import Aesop
import Babel.Util

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

/-- Run a MetaM action with an isolated heartbeat budget and catch failures/timeouts. -/
def tryWithHeartbeats (budget : Nat) (act : MetaM Bool) : MetaM Bool := do
  let saved ← saveState
  try
    withCurrHeartbeats do
      withOptions (fun o => o.set `maxHeartbeats budget) do
        act
  catch _ =>
    return false
  finally
    restoreState saved

/-- Level 1 gate: returns `true` iff `exact?` (`librarySearch`) CLOSES the goal. -/
def closedByExact? (stmtType : Expr) (budget : Nat) : MetaM Bool :=
  tryWithHeartbeats budget do
    let mvar ← mkFreshExprMVar stmtType
    let (_, goal) ← mvar.mvarId!.intros
    -- First check trivial assumption/rfl
    if (← goal.assumptionCore) then
      return true
    try
      goal.refl
      return true
    catch _ => pure ()
    -- Now run `exact?` (Lean's LibrarySearch)
    let res ← Lean.Meta.LibrarySearch.librarySearch goal
    return res.isNone

/-- Try closing a goal with `simp_all` / `simp`. -/
def closedBySimp (stmtType : Expr) (budget : Nat) : MetaM Bool :=
  tryWithHeartbeats budget do
    let mvar ← mkFreshExprMVar stmtType
    let (_, goal) ← mvar.mvarId!.intros
    let ctx ← Simp.mkContext
    let (res?, _) ← simpGoal goal ctx (simplifyTarget := true)
    match res? with
    | none => return true
    | some (_, g) =>
        if (← g.assumptionCore) then return true
        try g.refl; return true catch _ => return false

/-- Try closing a goal with `aesop`. -/
def closedByAesop (stmtType : Expr) (budget : Nat) : MetaM Bool :=
  tryWithHeartbeats budget do
    let mvar ← mkFreshExprMVar stmtType
    let (_, goal) ← mvar.mvarId!.intros
    let (goals, _) ← Aesop.search goal
    return goals.isEmpty

/-- Evaluate Levels 1, 2, and 3 on a shrunk `(stmtType, proofExpr)` pair. -/
def evaluateNovelty
    (stmtType : Expr)
    (proofExpr : Expr)
    (exactBudget : Nat)
    (aesopBudget : Nat) : MetaM NoveltyReport := do
  let exactClosed ← closedByExact? stmtType exactBudget
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
    if (← closedBySimp stmtType aesopBudget) then
      pure (some "simp")
    else if (← closedByAesop stmtType aesopBudget) then
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
