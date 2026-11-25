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

/-- Lemma applications in a term. Instances that are theorems are not counted: they are
    found by the elaborator and are no step of a derivation. -/
partial def lemmaCount (env : Environment) (e : Expr) : Nat :=
  match e with
  | .app .. =>
      let here := match e.getAppFn with
        | .const c _ =>
            if (env.find? c).any (· matches .thmInfo _) && !isInstanceCore env c then 1 else 0
        | fn => lemmaCount env fn
      e.getAppArgs.foldl (fun n arg => n + lemmaCount env arg) here
  | .lam _ type body _ => lemmaCount env type + lemmaCount env body
  | .mdata _ inner => lemmaCount env inner
  | _ => 0

/-- Every closed lemma application inside a proof with the fact it proves, outermost first. -/
partial def lemmaFacts (e : Expr) (acc : Array (Expr × Expr) := #[]) :
    MetaM (Array (Expr × Expr)) := do
  match e with
  | .app .. =>
      let mut acc := acc
      if let .const c _ := e.getAppFn then
        let env ← getEnv
        if (env.find? c).any (· matches .thmInfo _) && !isInstanceCore env c
            && !e.hasLooseBVars then
          acc := acc.push (e, ← instantiateMVars (← inferType e))
      for arg in e.getAppArgs do
        acc ← lemmaFacts arg acc
      return acc
  | .lam _ _ body _ => lemmaFacts body acc
  | .mdata _ inner => lemmaFacts inner acc
  | _ => return acc

/-- A proof of `fact` from the local hypotheses by assumption, reflexivity or one library
    lemma: what the Level 1 gate looks for, returned as a term. -/
def oneStepProof (fact : Expr) (budget : Nat) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    tryCatchRuntimeEx
      (withHeartbeatBudget budget do
        let mvar ← mkFreshExprMVar fact
        let goal := mvar.mvarId!
        let mut closed ← goal.assumptionCore
        if !closed then
          try
            goal.refl
            closed := true
          catch _ => pure ()
        if !closed then
          closed := (← goal.withContext (Lean.Meta.LibrarySearch.librarySearch goal)).isNone
        let proof ← instantiateMVars mvar
        return if closed && !proof.hasExprMVar && !proof.hasSorry then some proof else none)
      (fun _ => pure none)
  finally
    restoreState saved

/-- Does a derivation take a detour that its statement pays for?

    `body` is the proof with the theorem's binders opened as `xs`. A shortcut is a fact that
    the derivation reaches in two or more lemma steps although the hypotheses give it in
    one, or are it. Steps spent inside the fact's own statement are not counted. With the
    shortcut put in place of the detour, the proof may stop using a hypothesis, or stop
    using any lemma of the focus area: then the statement carries a hypothesis that does no
    work, or a subject that is decoration, and the answer is `true`. A detour that only
    lengthens the proof is tolerated. -/
def hasDefectiveShortcut (body : Expr) (xs : Array Expr) (isFocus : Name → Bool)
    (budget : Nat) : MetaM Bool := do
  let env ← getEnv
  let hyps ← xs.filterM fun x => do
    let decl ← x.fvarId!.getDecl
    return decl.binderInfo != .instImplicit && (← isProp decl.type)
  let focusLemmas := fun (e : Expr) =>
    (e.getUsedConstants.filter fun c =>
      (env.find? c).any (· matches .thmInfo _) && isFocus c).size
  let mut tried : Array Expr := #[]
  for (sub, fact) in ← lemmaFacts body do
    if sub == body || tried.contains sub then continue
    tried := tried.push sub
    if lemmaCount env sub < lemmaCount env fact + 2 then continue
    if (← isClass? fact).isSome then continue
    let some quick ← oneStepProof fact budget | continue
    let short := body.replace fun e => if e == sub then some quick else none
    let losesHypothesis := hyps.any fun h =>
      body.containsFVar h.fvarId! && !short.containsFVar h.fvarId!
    if losesHypothesis || (focusLemmas body > 0 && focusLemmas short == 0) then
      return true
  return false

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
