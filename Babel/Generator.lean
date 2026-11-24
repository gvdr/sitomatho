import Lean
import Std.Data.HashMap
import Babel.Util
import Babel.Gate

namespace Babel

open Lean Meta

/-- Precomputed head-symbol index over clean Mathlib theorems. -/
structure LemmaIndex where
  /-- Maps explicit-hypothesis head constant -> theorem names expecting such a hypothesis. -/
  byHypHead : Std.HashMap Name (Array Name)
  /-- Clean seed theorems with >= 1 explicit hypothesis. -/
  seeds : Array Name
  /-- Total indexed theorems. -/
  totalIndexed : Nat
deriving Inhabited

/-- Filter out internal, tactic, compiler, or degenerate declaration names. -/
def isCleanMathlibName (n : Name) : Bool :=
  if n.isInternal || n.isInternalDetail then false
  else
    let s := n.toString
    let badSubstr := [
      "_private", "._", ".match_", ".proof_", ".eq_", "noConfusion",
      "recOn", "casesOn", "brecOn", "below", "ibelow", "sizeOf",
      "congrArg", "autoParam", "optParam", "sorryAx", "Classical.em",
      "Lean.", "Tactic.", "Mathlib.Tactic.", "Aesop.", "Plausible.",
      "Qq.", "Batteries.Tactic.", "Init.Internal.", "Std.Internal.",
      "Lake.", "Elab.", "Meta."
    ]
    !badSubstr.any fun b => (s.splitOn b).length > 1

/-- Inspect leading `forallE` binders syntactically (no MetaM needed!) for fast indexing. -/
partial def inspectBinders (e : Expr) (totalBinders : Nat := 0) (hypHeads : Array Name := #[]) :
    Nat × Array Name × Option Name :=
  match e with
  | .forallE _ dom body bi =>
      let hypHeads' :=
        if bi == .default then
          match dom.getAppFn with
          | .const head _ =>
              if head == `True || head == `False then hypHeads
              else hypHeads.push head
          | _ => hypHeads
        else hypHeads
      inspectBinders body (totalBinders + 1) hypHeads'
  | concl =>
      let conclHead := match concl.getAppFn with
        | .const h _ => some h
        | _ => none
      (totalBinders, hypHeads, conclHead)

/-- Build the head-symbol index over the loaded environment once per run. -/
def buildLemmaIndex (env : Environment) : LemmaIndex := Id.run do
  let mut byHypHead : Std.HashMap Name (Array Name) := {}
  let mut seeds : Array Name := #[]
  let mut total := 0

  for (name, cinfo) in env.constants.map₁ do
    match cinfo with
    | .thmInfo info =>
        if !isCleanMathlibName name then continue
        if info.levelParams.length > 3 then continue
        let (nBinders, hypHeads, conclHead?) := inspectBinders info.type
        if nBinders == 0 || nBinders > 10 then continue
        if hypHeads.isEmpty || hypHeads.size > 4 then continue
        match conclHead? with
        | none => continue
        | some ch =>
            if ch == `True || ch == `False || ch == `Iff || ch == `PUnit || ch == `Unit then
              continue
            total := total + 1
            -- Deduplicate head symbols within a single theorem
            let mut seenLocal : NameSet := {}
            for h in hypHeads do
              if !seenLocal.contains h then
                seenLocal := seenLocal.insert h
                let arr := byHypHead.getD h #[]
                byHypHead := byHypHead.insert h (arr.push name)
            if hypHeads.size >= 1 && hypHeads.size <= 3 then
              seeds := seeds.push name
    | _ => continue

  return { byHypHead, seeds, totalIndexed := total }

/-- One step recorded during a random forward walk. -/
structure WalkStep where
  stepIdx : Nat
  lemmaName : Name
  namespaceName : String
  factType : Expr
  factProof : Expr
  parentSteps : Array Nat
deriving Inhabited

/-- Structured result emitted by Generator A. -/
structure WalkCandidate where
  seed : Nat
  stepsRequested : Nat
  stepsTaken : Nat
  statementLean : String
  statementPretty : String
  statementHash : String
  leanFile : String
  axioms : Array String
  namespaces : Array String
  depNodes : Array (String × String × String) -- (id, namespace, kind)
  depEdges : Array (String × String × String) -- (from, to, lemma)
  novelty : NoveltyReport
deriving Inhabited

/-- Reject trivial or degenerate conclusions (`True`, `False`, `x = x`). -/
def isInterestingConclusion (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasLevelMVar then return false
  if e.isConstOf `True || e.isConstOf `False then return false
  match e.eq? with
  | some (_, lhs, rhs) =>
      if lhs == rhs then return false
      return true
  | none => return true

/-- Check if an expression has a `Sort (param _)` directly (not `Sort (succ ...)`). -/
partial def hasBareSortParam (e : Expr) : Bool :=
  match e with
  | .sort (.param _) => true
  | .app f a => hasBareSortParam f || hasBareSortParam a
  | .lam _ t b _ => hasBareSortParam t || hasBareSortParam b
  | .forallE _ t b _ => hasBareSortParam t || hasBareSortParam b
  | .letE _ t v b _ => hasBareSortParam t || hasBareSortParam v || hasBareSortParam b
  | .mdata _ inner => hasBareSortParam inner
  | .proj _ _ inner => hasBareSortParam inner
  | _ => false

/-- Instantiate universe parameters cleanly: `Level.zero` for `Type u`, `Level.succ Level.zero` if bare `Sort u`. -/
def concreteLevels (info : TheoremVal) : List Level :=
  let lvl := if hasBareSortParam info.type then Level.succ Level.zero else Level.zero
  info.levelParams.map fun _ => lvl

/-- Check if an expression is already syntactically present in our derived facts. -/
def alreadyKnown (facts : Array WalkStep) (t : Expr) : Bool :=
  facts.any fun f => f.factType == t

/-- Weighted sample from candidate lemma names favoring untouched Mathlib namespaces. -/
def sampleCandidate
    (rng : Rng)
    (cands : Array Name)
    (usedNs : Array String)
    (lastLemma : Name)
    (interdiscWeight : Float) : Option Name × Rng := Id.run do
  if cands.isEmpty then return (none, rng)
  -- Sample up to 16 candidates uniformly, then do weighted choice by namespace novelty
  let sampleN := min 16 cands.size
  let mut pool : Array (Name × Float) := #[]
  let mut r := rng
  let mut totalW : Float := 0.0
  for _ in [:sampleN] do
    let (idx, r') := r.nextNat cands.size
    r := r'
    let cand := cands[idx]!
    if cand == lastLemma then continue
    let ns := topNamespace cand
    let w := if usedNs.contains ns then 1.0 else interdiscWeight
    pool := pool.push (cand, w)
    totalW := totalW + w
  if pool.isEmpty then
    return r.pickArray? cands
  let (u, r') := r.nextFloat
  let target := u * totalW
  let mut acc : Float := 0.0
  for (cand, w) in pool do
    acc := acc + w
    if acc >= target then
      return (some cand, r')
  return (pool.back?.map Prod.fst, r')

/-- Attempt one forward-chaining step applying lemma `L` to active fact `h`.
    Returns `(newFVars, newStep, rng)` if successful; introduces at most 2 new open hypotheses. -/
def tryApplyLemma
    (lemmaName : Name)
    (targetStep : WalkStep)
    (allSteps : Array WalkStep)
    (ctxFVars : Array Expr)
    (addedHypsSoFar : Nat)
    (nextStepIdx : Nat)
    (rng : Rng) :
    MetaM (Option (Array (Name × Expr × BinderInfo) × (Array Expr → MetaM (Option WalkStep))) × Rng) := do
  -- We resolve inside a fresh metavariable context; any newly required open hypotheses
  -- are returned as binder specs so the caller can `withLocalDecl` them cleanly!
  let env ← getEnv
  let some (.thmInfo info) := env.find? lemmaName | return (none, rng)
  let lvls := concreteLevels info
  let lemmaType := info.instantiateTypeLevelParams lvls
  let lemmaConst := mkConst lemmaName lvls

  let (mvars, binfos, conclType) ← forallMetaTelescope lemmaType

  -- Find an explicit binder whose type unifies with `targetStep.factType`
  let mut matchedIdx? : Option Nat := none
  for i in [:mvars.size] do
    if binfos[i]! == .default then
      let mtype ← inferType mvars[i]!
      if (← isDefEq mtype targetStep.factType) then
        if (← isDefEq mvars[i]! targetStep.factProof) then
          matchedIdx? := some i
          break

  let some matchedIdx := matchedIdx? | return (none, rng)

  -- Track which earlier steps were used to close other hypotheses
  let mut parentSteps : Array Nat := #[targetStep.stepIdx]
  let mut r := rng
  let mut openBinders : Array (Nat × Name × Expr × BinderInfo) := #[]

  -- Pass 1: try synthesizing typeclass instances and closing explicit args from context/steps
  for i in [:mvars.size] do
    if i == matchedIdx then continue
    let mv := mvars[i]!
    if (← mv.mvarId!.isAssigned) then continue
    let bi := binfos[i]!
    let mtype ← instantiateMVars (← inferType mv)

    if bi == .instImplicit then
      if !mtype.hasExprMVar then
        if let some inst ← synthInstance? mtype then
          let _ ← isDefEq mv inst
    else if bi == .default then
      -- First try closing from previously derived steps
      let mut closed := false
      for st in allSteps do
        if (← isDefEq mtype st.factType) then
          if (← isDefEq mv st.factProof) then
            if !parentSteps.contains st.stepIdx then
              parentSteps := parentSteps.push st.stepIdx
            closed := true
            break
      -- Next try closing from existing local context variables (Props or matching data)
      if !closed then
        let mut matchingFVars : Array Expr := #[]
        for fv in ctxFVars do
          let ft ← inferType fv
          let saved ← saveState
          if (← isDefEq mtype ft) then
            matchingFVars := matchingFVars.push fv
          restoreState saved
        if !matchingFVars.isEmpty then
          let (pick?, r') := r.pickArray? matchingFVars
          r := r'
          if let some fv := pick? then
            if (← isDefEq mv fv) then
              closed := true
      -- Otherwise, if type is fully concrete (no mvars) and we have budget, schedule an open binder
      if !closed then
        let mtype' ← instantiateMVars (← inferType mv)
        if !mtype'.hasExprMVar && !mtype'.hasLevelMVar then
          if addedHypsSoFar + openBinders.size < 4 then
            let isP ← isProp mtype'
            let bname :=
              if isP then Name.mkSimple s!"h_{nextStepIdx}_{i}"
              else Name.mkSimple s!"x_{nextStepIdx}_{i}"
            openBinders := openBinders.push (i, bname, mtype', .default)

  -- Pass 2: synthesize remaining typeclass instances now that explicit args may be known
  for i in [:mvars.size] do
    let mv := mvars[i]!
    if (← mv.mvarId!.isAssigned) then continue
    if binfos[i]! == .instImplicit then
      let mtype ← instantiateMVars (← inferType mv)
      if !mtype.hasExprMVar then
        if let some inst ← synthInstance? mtype then
          let _ ← isDefEq mv inst
      if !(← mv.mvarId!.isAssigned) then
        -- Reject: never invent unsolvable typeclasses on concrete types!
        return (none, r)

  -- Verify every mvar is either assigned OR scheduled to become a fresh open binder
  let openIndices := openBinders.map fun (idx, _, _, _) => idx
  for i in [:mvars.size] do
    let mv := mvars[i]!
    if !(← mv.mvarId!.isAssigned) && !openIndices.contains i then
      return (none, r)

  -- Check conclusion is free of unassigned mvars (except those from openBinders)
  let binderSpecs := openBinders.map fun (_, nm, tp, bi) => (nm, tp, bi)
  let mkStep : Array Expr → MetaM (Option WalkStep) := fun freshFVars => do
    if freshFVars.size != openBinders.size then return none
    for k in [:openBinders.size] do
      let (idx, _, _, _) := openBinders[k]!
      if !(← isDefEq mvars[idx]! freshFVars[k]!) then
        return none
    -- Final instance synthesis pass in case freshFVars resolved anything
    for i in [:mvars.size] do
      let mv := mvars[i]!
      if !(← mv.mvarId!.isAssigned) then
        if binfos[i]! == .instImplicit then
          let mtype ← instantiateMVars (← inferType mv)
          if let some inst ← synthInstance? mtype then
            let _ ← isDefEq mv inst
        if !(← mv.mvarId!.isAssigned) then
          return none

    let args ← mvars.mapM instantiateMVars
    let proof := mkAppN lemmaConst args
    let concl ← instantiateMVars conclType
    if proof.hasExprMVar || proof.hasLevelMVar || concl.hasExprMVar || concl.hasLevelMVar then
      return none
    if !(← isInterestingConclusion concl) then
      return none
    if alreadyKnown allSteps concl then
      return none
    try
      check proof
    catch _ =>
      return none
    return some {
      stepIdx := nextStepIdx
      lemmaName := lemmaName
      namespaceName := topNamespace lemmaName
      factType := concl
      factProof := proof
      parentSteps := parentSteps
    }

  return (some (binderSpecs, mkStep), r)

/-- Helper to recursively introduce `specs` via `withLocalDecl` and invoke continuation `k`. -/
def withLocalDeclsList {α : Type}
    (specs : List (Name × Expr × BinderInfo))
    (acc : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  match specs with
  | [] => k acc
  | (nm, tp, bi) :: rest =>
      withLocalDecl nm bi tp fun fv =>
        withLocalDeclsList rest (acc.push fv) k

/-- Produce a clean, non-hygienic, non-colliding Lean identifier for a binder. -/
def sanitizeBinderName (raw : Name) (bi : BinderInfo) (isP : Bool) (used : Std.HashSet String) (idx : Nat) : Name :=
  let base :=
    if bi == .instImplicit then s!"inst_{idx}"
    else if raw.hasMacroScopes || raw.isAnonymous || raw.isInternal then
      if isP then s!"h_{idx}" else s!"x_{idx}"
    else
      let s := raw.toString
      let ok := !s.isEmpty && s.all (fun c => c.isAlphanum || c == '_' || c == '\'' || c.toNat >= 0x3b1 && c.toNat <= 0x3c9)
      if ok && s != "_" && !s.startsWith "inst" then s
      else if isP then s!"h_{idx}" else s!"x_{idx}"
  Id.run do
    let mut cand := base
    let mut n := 1
    while used.contains cand do
      cand := s!"{base}_{n}"
      n := n + 1
    return Name.mkSimple cand

/-- Re-bind `usedFVars` with clean non-hygienic names so `ppExpr` never emits `✝` names,
    then render a standalone, self-contained `Result.lean` file. Returns `none` if the
    statement contains opaque proof ellipses (`⋯`). -/
def renderStandaloneLean
    (thmName : String)
    (usedFVars : Array Expr)
    (concl : Expr)
    (proof : Expr)
    (usedSteps : Array WalkStep) : MetaM (Option (String × String × String)) := do
  -- Abstract and immediately re-open with sanitized, unique, non-hygienic names
  let stmtClosed ← mkForallFVars usedFVars concl
  let proofClosed ← mkLambdaFVars usedFVars proof

  -- Compute clean binder names in order
  let mut cleanNames : Array Name := #[]
  let mut usedStrs : Std.HashSet String := {}
  let mut idx := 1
  for fv in usedFVars do
    let decl ← fv.fvarId!.getDecl
    let isP ← isProp decl.type
    let nm := sanitizeBinderName decl.userName decl.binderInfo isP usedStrs idx
    usedStrs := usedStrs.insert nm.toString
    cleanNames := cleanNames.push nm
    idx := idx + 1

  -- Open both statement and proof under a fresh local context with the clean names
  let rec openClean
      (names : List Name)
      (st : Expr)
      (pr : Expr)
      (accFVars : Array Expr) : MetaM (Option (String × String × String)) := do
    match names with
    | [] =>
      let cleanStmt ← mkForallFVars accFVars st
      let stmtPrettyFmt ← withOptions (fun o =>
          o.set `pp.unicode.fun true
          |>.set `pp.universes false
          |>.set `pp.explicit false) do
        ppExpr cleanStmt
      let stmtPretty := stmtPrettyFmt.pretty 92
      if (stmtPretty.splitOn "⋯").length > 1 then
        return none

      let mut binderLines : Array String := #[]
      for fv in accFVars do
        let decl ← fv.fvarId!.getDecl
        let tyFmt ← withOptions (fun o =>
            o.set `pp.unicode.fun true
            |>.set `pp.universes false) do
          ppExpr decl.type
        let tyStr := tyFmt.pretty 84
        if (tyStr.splitOn "⋯").length > 1 then
          return none
        let nmStr := decl.userName.toString
        let bStr := match decl.binderInfo with
          | .implicit => s!"\{{nmStr} : {tyStr}}"
          | .strictImplicit => s!"⦃{nmStr} : {tyStr}⦄"
          | .instImplicit => s!"[{nmStr} : {tyStr}]"
          | .default => s!"({nmStr} : {tyStr})"
        binderLines := binderLines.push s!"    {bStr}"

      let conclFmt ← withOptions (fun o =>
          o.set `pp.unicode.fun true
          |>.set `pp.universes false) do
        ppExpr st
      let conclStr := conclFmt.pretty 88
      if (conclStr.splitOn "⋯").length > 1 then
        return none

      let bindersBlock :=
        if binderLines.isEmpty then ""
        else "\n" ++ String.intercalate "\n" binderLines.toList

      let stmtDecl := s!"theorem {thmName}{bindersBlock} :\n    {conclStr}"

      let proofFmt ← withOptions (fun o =>
          o.set `pp.explicit true
          |>.set `pp.universes true
          |>.set `pp.proofs true
          |>.set `pp.unicode.fun true
          |>.set `pp.mvars false) do
        ppExpr pr
      let proofStr := proofFmt.pretty 96
      if (proofStr.splitOn "✝").length > 1 || (proofStr.splitOn "⋯").length > 1 then
        return none

      let stepComments := usedSteps.map fun s =>
        s!"-- Step {s.stepIdx}: {s.lemmaName} ({s.namespaceName})"
      let headerComment := String.intercalate "\n" stepComments.toList

      -- Collect the minimal set of Mathlib/Lean modules defining constants in statement & proof
      let env ← getEnv
      let allConsts := collectConsts cleanStmt |>.merge (collectConsts pr)
      let mut modSet : NameSet := {}
      for c in allConsts do
        if let some midx := env.getModuleIdxFor? c then
          if h : midx.toNat < env.header.moduleNames.size then
            let mname := env.header.moduleNames[midx.toNat]
            let s := mname.toString
            if !s.startsWith "Init" && !s.startsWith "Babel" then
              modSet := modSet.insert mname
      let modList := modSet.toList.mergeSort (fun a b => a.toString < b.toString)
      let importsBlock :=
        if modList.isEmpty then "import Mathlib.Init\n"
        else String.intercalate "\n" (modList.map fun m => s!"import {m}") ++ "\n"

      let fullFile :=
        importsBlock ++ "\n" ++
        "set_option autoImplicit false\n" ++
        "set_option linter.unusedVariables false\n\n" ++
        headerComment ++ "\n" ++
        stmtDecl ++ " :=\n" ++
        "  " ++ proofStr ++ "\n"

      return some (stmtDecl, stmtPretty, fullFile)
    | nm :: rest =>
      match st, pr with
      | .forallE _ dom body bi, .lam _ _ pbody _ =>
          withLocalDecl nm bi dom fun fv =>
            openClean rest (body.instantiate1 fv) (pbody.instantiate1 fv) (accFVars.push fv)
      | _, _ => return none

  openClean cleanNames.toList stmtClosed proofClosed #[]

/-- Recursive driver executing steps `stepNum .. targetSteps` inside nested `withLocalDecl` scopes. -/
partial def runWalkLoop
    (idx : LemmaIndex)
    (seed : Nat)
    (targetSteps : Nat)
    (interdiscWeight : Float)
    (exactBudget : Nat)
    (aesopBudget : Nat)
    (ctxFVars : Array Expr)
    (steps : Array WalkStep)
    (addedHyps : Nat)
    (rng : Rng) : MetaM (Option WalkCandidate × Rng) := do
  if steps.size >= targetSteps then
    -- Finished walk! Shrink unused hypotheses & unused intermediate steps.
    let some finalStep := steps.back? | return (none, rng)
    let seedFVars := collectFVarsExpr finalStep.factType (collectFVarsExpr finalStep.factProof)
    let keptIds ← closeFVarsTransitively seedFVars
    let usedFVars := ctxFVars.filter fun fv => keptIds.contains fv.fvarId!

    -- Abstract shrunk theorem statement & proof
    let stmtType ← mkForallFVars usedFVars finalStep.factType
    let fullProof ← mkLambdaFVars usedFVars finalStep.factProof
    if stmtType.hasExprMVar || fullProof.hasExprMVar || stmtType.hasLevelMVar || fullProof.hasLevelMVar then
      return (none, rng)

    -- Verify kernel typecheck and axioms strictly
    try
      check fullProof
    catch _ =>
      return (none, rng)

    let axs ← collectExprAxioms fullProof
    if !axiomsAreClean axs then
      return (none, rng)

    -- Evaluate Level 1 gate (`exact?`), Level 2 (`simp`/`aesop`), Level 3 (depth ratio)
    let nov ← evaluateNovelty stmtType fullProof exactBudget aesopBudget
    if !nov.level1ExactFailed then
      return (none, rng)

    -- Prune walk steps to those reachable from `finalStep`
    let mut keepSteps : Std.HashSet Nat := {}
    let mut q : List Nat := [finalStep.stepIdx]
    while !q.isEmpty do
      match q with
      | [] => break
      | s :: rest =>
          q := rest
          if keepSteps.contains s then continue
          keepSteps := keepSteps.insert s
          if let some st := steps.find? (fun x => x.stepIdx == s) then
            for p in st.parentSteps do
              if !keepSteps.contains p then q := p :: q

    let usedSteps := steps.filter fun st => keepSteps.contains st.stepIdx
    -- Require at least 2 connected Mathlib steps in the shrunk proof
    if usedSteps.size < 2 then
      return (none, rng)

    let some (stmtDecl, stmtPretty, leanFile) ←
      renderStandaloneLean "akcm_candidate" usedFVars finalStep.factType finalStep.factProof usedSteps
      | return (none, rng)

    -- Collect unique namespaces & dependency graph
    let mut nsArr : Array String := #[]
    let mut nodes : Array (String × String × String) := #[]
    let mut edges : Array (String × String × String) := #[]
    let mut seenNodes : Std.HashSet String := {}
    for st in usedSteps do
      if !nsArr.contains st.namespaceName then
        nsArr := nsArr.push st.namespaceName
      let nodeId := st.lemmaName.toString
      if !seenNodes.contains nodeId then
        seenNodes := seenNodes.insert nodeId
        nodes := nodes.push (nodeId, st.namespaceName, "mathlib")
      for p in st.parentSteps do
        if let some pst := usedSteps.find? (fun x => x.stepIdx == p) then
          edges := edges.push (pst.lemmaName.toString, nodeId, s!"step_{st.stepIdx}")

    let cand : WalkCandidate := {
      seed := seed
      stepsRequested := targetSteps
      stepsTaken := usedSteps.size
      statementLean := stmtDecl
      statementPretty := stmtPretty
      statementHash := canonicalHash stmtType
      leanFile := leanFile
      axioms := axs.map Name.toString
      namespaces := nsArr
      depNodes := nodes
      depEdges := edges
      novelty := nov
    }
    return (some cand, rng)

  -- Otherwise attempt the next forward step
  let mut r := rng
  -- 75% bias toward extending the most recent step for deep connected chains
  let (u, r') := r.nextFloat
  r := r'
  let (targetStep, rAfterPick) :=
    if u < 0.75 || steps.size == 1 then (steps.back!, r)
    else
      let (idxPick, r'') := r.nextNat steps.size
      (steps[idxPick]!, r'')
  r := rAfterPick

  let headName? := targetStep.factType.getAppFn.constName?
  let some headName := headName? | do
    -- Dead end: if we already have >= 3 steps, finish early!
    if steps.size >= 3 then
      return ← runWalkLoop idx seed steps.size interdiscWeight exactBudget aesopBudget ctxFVars steps addedHyps r
    else
      return (none, r)

  let cands := idx.byHypHead.getD headName #[]
  if cands.isEmpty then
    if steps.size >= 3 then
      return ← runWalkLoop idx seed steps.size interdiscWeight exactBudget aesopBudget ctxFVars steps addedHyps r
    else
      return (none, r)

  let usedNs := steps.map (·.namespaceName)
  let lastLemma := targetStep.lemmaName

  -- Try up to 18 candidate lemmas
  for _ in [:18] do
    let (candOpt, r') := sampleCandidate r cands usedNs lastLemma interdiscWeight
    r := r'
    let some candName := candOpt | continue
    let saved ← saveState
    let (resOpt, r'') ← tryApplyLemma candName targetStep steps ctxFVars addedHyps steps.size r
    r := r''
    match resOpt with
    | none =>
        restoreState saved
    | some (binderSpecs, mkStep) =>
        let stepRes ← withLocalDeclsList binderSpecs.toList #[] fun freshFVars => do
          match ← mkStep freshFVars with
          | none => return none
          | some newStep =>
              let (finalOpt, _) ← runWalkLoop
                idx seed targetSteps interdiscWeight exactBudget aesopBudget
                (ctxFVars ++ freshFVars)
                (steps.push newStep)
                (addedHyps + freshFVars.size)
                r
              return finalOpt
        match stepRes with
        | some finalCand => return (some finalCand, r)
        | none => restoreState saved

  -- Couldn't extend further; if we reached >= 3 steps, try finishing here
  if steps.size >= 3 then
    runWalkLoop idx seed steps.size interdiscWeight exactBudget aesopBudget ctxFVars steps addedHyps r
  else
    return (none, r)

/-- Start a single random forward walk from a random Mathlib seed theorem. -/
def runSingleWalk
    (idx : LemmaIndex)
    (seed : Nat)
    (minSteps maxSteps : Nat)
    (interdiscWeight : Float)
    (exactBudget aesopBudget : Nat)
    (rng : Rng) : MetaM (Option WalkCandidate × Rng) := do
  let (seedNameOpt, r1) := rng.pickArray? idx.seeds
  let some seedName := seedNameOpt | return (none, r1)
  let (targetSteps, r2) := r1.nextRange minSteps maxSteps

  let env ← getEnv
  let some (.thmInfo info) := env.find? seedName | return (none, r2)
  let lvls := concreteLevels info
  let seedType := info.instantiateTypeLevelParams lvls
  let seedConst := mkConst seedName lvls

  forallTelescope seedType fun fvars concl => do
    if !(← isInterestingConclusion concl) then
      return (none, r2)
    let proof0 := mkAppN seedConst fvars
    try
      check proof0
    catch _ =>
      return (none, r2)

    let step0 : WalkStep := {
      stepIdx := 0
      lemmaName := seedName
      namespaceName := topNamespace seedName
      factType := concl
      factProof := proof0
      parentSteps := #[]
    }
    runWalkLoop idx seed targetSteps interdiscWeight exactBudget aesopBudget fvars #[step0] 0 r2

end Babel
