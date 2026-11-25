import Lean
import Lean.Meta.DiscrTree.Main
import Std.Data.HashMap
import Babel.Util
import Babel.Stats
import Babel.Gate
import Babel.Interest
import Babel.Convolute

namespace Babel

open Lean Meta

structure SpecialistSearch where
  focus : Name
  /-- Minimum retained derivation steps. -/
  minSteps : Nat := 4
  /-- Minimum distinct concepts (head predicates) among the retained steps. -/
  minConcepts : Nat := 3
  /-- Minimum retained steps whose lemma is defined under the focus. The seed is one of them,
      so the default asks for nothing more and a floor of two asks for one further on-topic step. -/
  minFocusSteps : Nat := 1
  trialsPerWalk : Nat := 240
  /-- How many of a walk's best derivations are offered to the gates. -/
  keep : Nat := 3
  limits : StepLimits := {}
deriving Inhabited

structure SpecialistProgress where
  maxDepth : Nat := 0
  maxJoinedDepth : Nat := 0
deriving Inhabited

def definingModule (env : Environment) (decl : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? decl
  env.header.moduleNames[moduleIdx.toNat]?

/-- Precomputed head-symbol index over clean Mathlib theorems. -/
structure LemmaIndex where
  /-- Maps explicit-hypothesis head constant -> theorem names expecting such a hypothesis. -/
  byHypHead : Std.HashMap Name (Array Name)
  /-- Clean seed theorems with >= 1 explicit hypothesis. -/
  seeds : Array Name
  /-- Total indexed theorems. -/
  totalIndexed : Nat
  bySpecialistHypHead : Std.HashMap Name (Array Name) := {}
  specialistSeeds : Array Name := #[]
  indexedLemmas : Array Name := #[]
  multiPremiseLemmas : NameSet := {}
  /-- Head constant of each indexed lemma's conclusion. -/
  conclHead : Std.HashMap Name Name := {}
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
      "Lake.", "Elab.", "Meta.",
      -- Auto-generated congruence and injectivity lemmas: they only restate equalities.
      "congr_simp", "injEq"
    ]
    !badSubstr.any fun b => (s.splitOn b).length > 1

/-- Modules whose declarations are logical, basic order, or basic set vocabulary. -/
def isLogicModule (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Init" || s.startsWith "Mathlib.Logic" || s.startsWith "Mathlib.Order.Defs"
    || s == "Mathlib.Order.Notation" || s == "Mathlib.Order.Basic" || s == "Mathlib.Data.Set.Defs"

/-- A lemma whose whole statement is in logical, basic order and basic set vocabulary, such
    as `ne_of_eq_of_ne`, `not_or_intro` or `Set.mem_of_eq_of_mem`. Such a step adds length without mathematical content. -/
def isGlueLemma (env : Environment) (lemmaName : Name) : Bool :=
  match env.find? lemmaName with
  | none => false
  | some info => info.type.getUsedConstants.all fun c =>
      match definingModule env c with
      | some m => isLogicModule m
      | none => false

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
def buildLemmaIndex (env : Environment) (focus : Option Name := none) : LemmaIndex := Id.run do
  let mut byHypHead : Std.HashMap Name (Array Name) := {}
  let mut seeds : Array Name := #[]
  let mut total := 0
  let mut bySpecialistHypHead : Std.HashMap Name (Array Name) := {}
  let mut specialistSeeds : Array Name := #[]
  let mut indexedLemmas : Array Name := #[]
  let mut multiPremiseLemmas : NameSet := {}
  let mut conclHead : Std.HashMap Name Name := {}

  for (name, cinfo) in env.constants.map₁ do
    match cinfo with
    | .thmInfo info =>
        -- A deprecated alias would let one lemma be applied twice under two names.
        if !isCleanMathlibName name || isGlueLemma env name || Linter.isDeprecated env name then continue
        let specialist := focus.any fun root => (definingModule env name).any root.isPrefixOf
        if info.levelParams.length > (if specialist then 8 else 3) then continue
        let (nBinders, hypHeads, conclHead?) := inspectBinders info.type
        if nBinders == 0 || nBinders > (if specialist then 24 else 10) then continue
        if hypHeads.isEmpty || hypHeads.size > (if specialist then 8 else 4) then continue
        match conclHead? with
        | none => continue
        | some ch =>
            if ch == `True || ch == `False || ch == `Iff || ch == `PUnit || ch == `Unit then
              continue
            total := total + 1
            conclHead := conclHead.insert name ch
            if specialist then
              specialistSeeds := specialistSeeds.push name
            if focus.isSome then
              indexedLemmas := indexedLemmas.push name
              if hypHeads.size >= 2 then
                multiPremiseLemmas := multiPremiseLemmas.insert name
            -- Deduplicate head symbols within a single theorem
            let mut seenLocal : NameSet := {}
            for h in hypHeads do
              if !seenLocal.contains h then
                seenLocal := seenLocal.insert h
                let arr := byHypHead.getD h #[]
                byHypHead := byHypHead.insert h (arr.push name)
                if specialist then
                  let arr := bySpecialistHypHead.getD h #[]
                  bySpecialistHypHead := bySpecialistHypHead.insert h (arr.push name)
            if hypHeads.size >= 1 && hypHeads.size <= 3 then
              seeds := seeds.push name
    | _ => continue

  return {
    byHypHead, seeds, totalIndexed := total, bySpecialistHypHead
    specialistSeeds, indexedLemmas, multiPremiseLemmas, conclHead
  }

/-- One step recorded during a random forward walk. -/
structure WalkStep where
  stepIdx : Nat
  lemmaName : Name
  namespaceName : String
  factType : Expr
  factProof : Expr
  parentSteps : Array Nat
  /-- Head constant of `factType`; what the step is "about". -/
  concept : Option Name := none
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
  depNodes : Array (String × String × String) -- (step id, lemma, namespace)
  depEdges : Array (String × String × String) -- (from, to, lemma)
  proofDepth : Nat
  proofJoins : Nat
  specialistSymbols : Array Name
  novelty : NoveltyReport
  /-- Recomputed on the finished derivation: `simp` cannot shrink the conclusion. -/
  simpNormal : Bool := true
  /-- Recomputed on the finished proof: lemma applications that take one proof for two premises. -/
  premiseReuse : Nat := 0
  components : InterestComponents := {}
  interestScore : Float := 0.0
  /-- Expression nodes of the conclusion alone, the quantity `maxFactSize` caps. -/
  conclusionSize : Nat := 0
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

/-- Lemma names of the given steps and all their ancestors, each step once.
    Steps are looked up by `stepIdx`, so the array may be in any order. -/
def ancestorLemmas (allSteps : Array WalkStep) (parents : Array Nat) : Array Name := Id.run do
  let mut pending := parents.toList
  let mut visited : Array Nat := #[]
  let mut lemmas : Array Name := #[]
  let mut fuel := allSteps.size * allSteps.size + parents.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    match pending with
    | [] => break
    | idx :: rest =>
        pending := rest
        if visited.contains idx then continue
        visited := visited.push idx
        if let some st := allSteps.find? (·.stepIdx == idx) then
          lemmas := lemmas.push st.lemmaName
          pending := st.parentSteps.toList ++ pending
  return lemmas

/-- Whether some lemma occurs more than `cap` times in `lemmas`. -/
def exceedsRepeatCap (lemmas : Array Name) (cap : Nat) : Bool :=
  lemmas.any fun name => (lemmas.filter (· == name)).size > cap

/-- Count lemma applications inside a proof term that receive the same proof for two
    explicit premises, such as `inter_mem h h`. -/
partial def countPremiseReuse (e : Expr) : MetaM Nat := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if args.isEmpty || !fn.isConst then return 0
  let info ← getFunInfoNArgs fn args.size
  let mut total := 0
  let mut proofs : Array Expr := #[]
  for i in [:args.size] do
    if h : i < info.paramInfo.size then
      let param := info.paramInfo[i]
      if param.isProp && param.binderInfo == .default then
        let arg := args[i]!
        if proofs.contains arg then
          total := total + 1
        proofs := proofs.push arg
        total := total + (← countPremiseReuse arg)
  return total

/-- A fact fills a hypothesis when the two statements agree up to instance-reducible
    unfolding, the standard `rw` and `simp` apply. Default transparency would also unfold
    definitions such as `Set α := α → Prop` and derive statements nobody would write. -/
private def matchArgument (mvar expectedType proof actualType : Expr) : MetaM Bool := do
  let saved ← saveState
  if (← withTransparency .instances (isDefEq expectedType actualType)) && (← isDefEq mvar proof) then
    return true
  restoreState saved
  return false

/-- Apply a lemma to a derived fact, reusing other facts and local hypotheses where possible. -/
def tryApplyLemma
    (stats : StatsRef)
    (limits : StepLimits)
    (lemmaName : Name)
    (targetStep : WalkStep)
    (allSteps : Array WalkStep)
    (ctxFVars : Array Expr)
    (addedHypsSoFar : Nat)
    (nextStepIdx : Nat)
    (rng : Rng) :
    MetaM (Option (Array (Name × Expr × BinderInfo) × (Array Expr → MetaM (Option WalkStep))) × Rng) := do
  -- Premises no existing fact fills become new variables and hypotheses of the theorem.
  -- They are returned as `(name, metavariable, binder info)` specs; the caller opens them
  -- with `withOpenedBinders` and then builds the step with the returned function.
  stats.modify fun s => { s with applicationsTried := s.applicationsTried + 1 }
  let env ← getEnv
  let some (.thmInfo info) := env.find? lemmaName | return (none, rng)
  -- Cheap test before any unification: the fact being extended already descends from this lemma.
  let onTargetPath := (ancestorLemmas allSteps #[targetStep.stepIdx]).filter (· == lemmaName)
  if onTargetPath.size >= limits.maxLemmaRepeats then
    stats.reject .repeatedLemma
    return (none, rng)
  let lvls := concreteLevels info
  let lemmaType := info.instantiateTypeLevelParams lvls
  let lemmaConst := mkConst lemmaName lvls

  let (mvars, binfos, conclType) ← forallMetaTelescope lemmaType

  -- Find an explicit binder whose type unifies with `targetStep.factType`
  let mut matchedIdx? : Option Nat := none
  for i in [:mvars.size] do
    if binfos[i]! == .default then
      let mtype ← inferType mvars[i]!
      if ← matchArgument mvars[i]! mtype targetStep.factProof targetStep.factType then
        matchedIdx? := some i
        break

  let some matchedIdx := matchedIdx? | do
    stats.reject .noUnifier
    return (none, rng)

  -- Track which earlier steps were used to close other hypotheses
  let mut parentSteps : Array Nat := #[targetStep.stepIdx]
  -- Proofs already filling a premise of this application. A proof fills at most one premise;
  -- otherwise closure lemmas turn one fact into `s ∩ s`.
  let mut usedProofs : Array Expr := #[targetStep.factProof]
  let mut r := rng

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
        if usedProofs.contains st.factProof then continue
        if ← matchArgument mv mtype st.factProof st.factType then
          if !parentSteps.contains st.stepIdx then
            parentSteps := parentSteps.push st.stepIdx
          usedProofs := usedProofs.push st.factProof
          closed := true
          break
      -- Next try closing from existing local context variables (Props or matching data)
      if !closed then
        let mut matchingFVars : Array Expr := #[]
        for fv in ctxFVars do
          if usedProofs.contains fv then continue
          let ft ← inferType fv
          let saved ← saveState
          if (← withTransparency .instances (isDefEq mtype ft)) then
            matchingFVars := matchingFVars.push fv
          restoreState saved
        if !matchingFVars.isEmpty then
          let (pick?, r') := r.pickArray? matchingFVars
          r := r'
          if let some fv := pick? then
            if (← isDefEq mv fv) then
              if ← isProof fv then
                usedProofs := usedProofs.push fv
              closed := true

  -- Pass 1b: whatever is still unassigned becomes a new variable or hypothesis, taken in
  -- telescope order so that each type only mentions binders opened before it.
  let mut openBinders : Array (Nat × Name × BinderInfo) := #[]
  let mut openIds : Array MVarId := #[]
  for i in [:mvars.size] do
    let mv := mvars[i]!
    if (← mv.mvarId!.isAssigned) || binfos[i]! == .instImplicit then continue
    let mtype ← instantiateMVars (← inferType mv)
    let pending ← getMVars mtype
    -- No new types or type families, no type that depends on something left undetermined,
    -- and a bound on how many assumptions one derivation may add.
    let isTypeFamily ← forallTelescope mtype fun _ body => pure body.isSort
    if isTypeFamily || mtype.hasLevelMVar || pending.any (fun id => !openIds.contains id)
        || addedHypsSoFar + openBinders.size >= limits.maxNewBinders then
      stats.reject .unresolved
      return (none, r)
    let bname :=
      if ← isProp mtype then Name.mkSimple s!"h_{nextStepIdx}_{i}"
      else Name.mkSimple s!"x_{nextStepIdx}_{i}"
    openBinders := openBinders.push (i, bname, binfos[i]!)
    openIds := openIds.push mv.mvarId!

  -- Pass 2: synthesize remaining typeclass instances now that explicit args may be known
  for i in [:mvars.size] do
    let mv := mvars[i]!
    if (← mv.mvarId!.isAssigned) then continue
    if binfos[i]! == .instImplicit then
      let mtype ← instantiateMVars (← inferType mv)
      if !mtype.hasExprMVar then
        if let some inst ← synthInstance? mtype then
          let _ ← isDefEq mv inst
      if !(← mv.mvarId!.isAssigned) && !mtype.hasExprMVar then
        -- Reject: never invent unsolvable typeclasses on concrete types!
        stats.reject .unresolved
        return (none, r)

  -- The new step's whole ancestry, itself included: joining two branches must not bring
  -- the same lemma in from both sides.
  if exceedsRepeatCap ((ancestorLemmas allSteps parentSteps).push lemmaName) limits.maxLemmaRepeats then
    stats.reject .repeatedLemma
    return (none, r)

  -- Check conclusion is free of unassigned mvars (except those from openBinders)
  let binderSpecs := openBinders.map fun (idx, nm, bi) => (nm, mvars[idx]!, bi)
  let mkStep : Array Expr → MetaM (Option WalkStep) := fun freshFVars => do
    if freshFVars.size != openBinders.size then return none
    -- `withOpenedBinders` has assigned the opened metavariables; instances that depend on
    -- the new binders can be synthesized now.
    for i in [:mvars.size] do
      let mv := mvars[i]!
      if !(← mv.mvarId!.isAssigned) then
        if binfos[i]! == .instImplicit then
          let mtype ← instantiateMVars (← inferType mv)
          if let some inst ← synthInstance? mtype then
            let _ ← isDefEq mv inst
        if !(← mv.mvarId!.isAssigned) then
          stats.reject .unresolved
          return none

    let args ← mvars.mapM instantiateMVars
    let proof := mkAppN lemmaConst args
    let concl ← instantiateMVars conclType
    if proof.hasExprMVar || proof.hasLevelMVar || concl.hasExprMVar || concl.hasLevelMVar then
      stats.reject .unresolved
      return none
    if !(← isInterestingConclusion concl) || alreadyKnown allSteps concl then
      stats.reject .dullConclusion
      return none
    if exprSize concl > limits.maxFactSize then
      stats.reject .sizeCap
      return none
    -- Safety net behind `usedProofs`: no two explicit premises may be the same proof.
    let mut premises : Array Expr := #[]
    for i in [:args.size] do
      if binfos[i]! == .default && (← isProof args[i]!) then
        if premises.contains args[i]! then
          stats.reject .selfReuse
          return none
        premises := premises.push args[i]!
    try
      check proof
    catch _ =>
      stats.reject .kernelCheck
      return none
    if ← isPaddedFact concl limits.simpBudget then
      stats.reject .paddedFact
      return none
    stats.modify fun s => { s with applicationsSucceeded := s.applicationsSucceeded + 1 }
    return some {
      stepIdx := nextStepIdx
      lemmaName := lemmaName
      namespaceName := topNamespace lemmaName
      factType := concl
      factProof := proof
      parentSteps := parentSteps
      concept := conceptOf concl
    }

  return (some (binderSpecs, mkStep), r)

/-- Open new binders for the metavariables in `specs`, in order, and run `k` on them.
    Each metavariable is assigned its fresh variable directly: `isDefEq` would refuse, because
    the variable is declared after the metavariable and so lies outside its scope. The
    assignment is sound here since `k` builds and kernel-checks the term inside this scope.
    Returns `none` when a type is still undetermined at the moment its binder is opened, or
    when a new hypothesis is trivial, contradictory or padded. -/
def withOpenedBinders {α : Type}
    (stats : StatsRef)
    (specs : List (Name × Expr × BinderInfo))
    (acc : Array Expr)
    (k : Array Expr → MetaM (Option α)) : MetaM (Option α) := do
  match specs with
  | [] => k acc
  | (nm, mv, bi) :: rest =>
      let ty ← instantiateMVars (← inferType mv)
      if ty.hasExprMVar || ty.hasLevelMVar then return none
      if (← isProp ty) && (← isDegenerateHypothesis ty) then
        stats.reject .paddedFact
        return none
      withLocalDecl nm bi ty fun fv => do
        mv.mvarId!.assign fv
        withOpenedBinders stats rest (acc.push fv) k

/-- Produce a clean, non-hygienic, non-colliding Lean identifier for a binder. -/
def sanitizeBinderName (raw : Name) (bi : BinderInfo) (isP : Bool) (used : Std.HashSet String) (idx : Nat) : Name :=
  -- Binders the walk introduced are named `x_<step>_<arg>` / `h_<step>_<arg>`; give the
  -- variables a free letter so the statement reads like one a person wrote.
  let machineNamed :=
    let s := raw.toString
    (s.startsWith "x_" || s.startsWith "h_") && (s.drop 2).all fun c => c.isDigit || c == '_'
  let freeLetter := ["u", "v", "w", "a", "b", "c", "d", "e", "p", "q", "r"].find? fun l => !used.contains l
  let base :=
    if bi == .instImplicit then s!"inst_{idx}"
    else if raw.hasMacroScopes || raw.isAnonymous || raw.isInternal || machineNamed then
      if isP then s!"h_{idx}" else freeLetter.getD s!"x_{idx}"
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

/-- Open exactly `nBinders` binders of a closed statement and its proof under clean,
    unique, non-hygienic names, then render a standalone, self-contained `Result.lean`.
    Whatever follows those binders is the conclusion, also when it is itself a `∀`.
    Returns `none` if a printed term contains proof ellipses (`⋯`) or hygienic names (`✝`). -/
def renderStandaloneClosed
    (thmName : String)
    (stmtClosed proofClosed : Expr)
    (nBinders : Nat)
    (stepLabels : Array (Nat × Name × String))
    (convoluteDepth : Nat)
    (seed : Nat)
    (explicitStatement : Bool := false) : MetaM (Option (String × String × String)) := do
  let statementOptions (options : Options) :=
    options.set `pp.unicode.fun true
      |>.set `pp.universes explicitStatement
      |>.set `pp.explicit explicitStatement
      |>.set `pp.proofs explicitStatement

  let rec openClean
      (remaining : Nat)
      (st : Expr)
      (pr : Expr)
      (accFVars : Array Expr)
      (usedStrs : Std.HashSet String) : MetaM (Option (String × String × String)) := do
    match remaining with
    | 0 =>
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
        let tyFmt ← withOptions statementOptions (ppExpr decl.type)
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

      let conclFmt ← withOptions statementOptions (ppExpr st)
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

      let stepComments := stepLabels.map fun (stepIdx, lemmaName, namespaceName) =>
        s!"-- Step {stepIdx}: {lemmaName} ({namespaceName})"
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

      let proofBody := renderBaroqueTacticProof proofStr convoluteDepth seed

      let fullFile :=
        importsBlock ++ "\n" ++
        "set_option autoImplicit false\n" ++
        "set_option linter.unusedVariables false\n\n" ++
        headerComment ++ "\n" ++
        stmtDecl ++ " := " ++ proofBody

      return some (stmtDecl, stmtPretty, fullFile)
    | remaining + 1 =>
      match st, pr with
      | .forallE rawName dom body bi, .lam _ _ pbody _ =>
          let isP ← isProp dom
          let nm := sanitizeBinderName rawName bi isP usedStrs (accFVars.size + 1)
          withLocalDecl nm bi dom fun fv =>
            openClean remaining (body.instantiate1 fv) (pbody.instantiate1 fv)
              (accFVars.push fv) (usedStrs.insert nm.toString)
      | _, _ => return none

  openClean nBinders stmtClosed proofClosed #[] {}

/-- Ancestors include the step itself. Walk IDs are indices in topological order. -/
structure ProofShape where
  ancestors : Array (Std.HashSet Nat) := #[]
  depths : Array Nat := #[]
  joins : Nat := 0

def proofShape (steps : Array WalkStep) : ProofShape := Id.run do
  let mut shape : ProofShape := {}
  for st in steps do
    let mut ancestors : Std.HashSet Nat := ({} : Std.HashSet Nat).insert st.stepIdx
    let mut depth := 1
    for p in st.parentSteps do
      ancestors := (shape.ancestors[p]!).fold (fun acc n => acc.insert n) ancestors
      depth := max depth (shape.depths[p]! + 1)
    shape := { shape with
      ancestors := shape.ancestors.push ancestors
      depths := shape.depths.push depth }
  let retained := shape.ancestors.back?.getD {}
  let joins := steps.countP fun st =>
    retained.contains st.stepIdx && st.parentSteps.any fun p =>
      st.parentSteps.any fun q =>
        !(shape.ancestors[p]!).contains q && !(shape.ancestors[q]!).contains p
  return { shape with joins }

/-- A finished derivation closed over its hypotheses, so it stays valid after the local
    context it was found in is gone. The search keeps these and gates only the best. -/
structure KeptDerivation where
  stmtClosed : Expr
  proofClosed : Expr
  /-- Leading binders of `stmtClosed` that are hypotheses; the rest is the conclusion. -/
  nBinders : Nat
  /-- Retained steps: index, lemma, namespace. -/
  stepLabels : Array (Nat × Name × String)
  /-- Dependency edges between retained steps: parent, child, lemma. -/
  edges : Array (Nat × Nat × Name)
  depth : Nat
  components : InterestComponents
  score : Float
  specialistSymbols : Array Name
  stmtHash : String
deriving Inhabited

/-- Which specialist floor a derivation misses, if any. -/
def specialistShortfall (search : SpecialistSearch) (steps concepts focusSteps : Nat) :
    Option Reject :=
  if steps < search.minSteps then some .fewSteps
  else if concepts < search.minConcepts then some .fewConcepts
  else if focusSteps < search.minFocusSteps then some .fewFocusSteps
  else none

/-- The lemmas of `pool` that satisfy `isFocus`, or the whole pool when none does. -/
def preferFocus (pool : Array Name) (isFocus : Name → Bool) : Array Name :=
  let focused := pool.filter isFocus
  if focused.isEmpty then pool else focused

/-- Close a derivation over the hypotheses it uses and score it. Cheap: no gate runs here.
    In specialist mode the derivation must have enough retained steps, concepts and on-topic
    steps, and a conclusion that mentions a symbol defined under the focus. -/
def closeDerivation
    (ctxFVars : Array Expr)
    (steps : Array WalkStep)
    (specialist : Option SpecialistSearch)
    (stats : StatsRef) : MetaM (Option KeptDerivation) := do
  let shape := proofShape steps
  let some finalStep := steps.back? | return none
  let retained := shape.ancestors.back?.getD {}
  let usedSteps := steps.filter fun st => retained.contains st.stepIdx
  if usedSteps.size < 2 then
    stats.reject .fewSteps
    return none
  let concepts := countDistinct (usedSteps.map (·.concept))
  let env ← getEnv
  let focusSteps := match specialist with
    | some search => usedSteps.countP fun st =>
        (definingModule env st.lemmaName).any search.focus.isPrefixOf
    | none => 0
  let mut specialistSymbols := #[]
  if let some search := specialist then
    if let some shortfall := specialistShortfall search usedSteps.size concepts focusSteps then
      stats.reject shortfall
      return none
    specialistSymbols := ((collectConsts finalStep.factType).toList.filter fun decl =>
      (definingModule env decl).any search.focus.isPrefixOf).toArray
    if specialistSymbols.isEmpty then
      stats.reject .noFocusSymbol
      return none

  -- Keep only the hypotheses the final fact depends on.
  let seedFVars := collectFVarsExpr finalStep.factType (collectFVarsExpr finalStep.factProof)
  let keptIds ← closeFVarsTransitively seedFVars
  let usedFVars := ctxFVars.filter fun fv => keptIds.contains fv.fvarId!
  let stmtClosed ← mkForallFVars usedFVars finalStep.factType
  let proofClosed ← mkLambdaFVars usedFVars finalStep.factProof
  if stmtClosed.hasExprMVar || proofClosed.hasExprMVar || stmtClosed.hasLevelMVar
      || proofClosed.hasLevelMVar || stmtClosed.hasFVar || proofClosed.hasFVar then
    stats.reject .kernelCheck
    return none
  -- A hypothesis about variables the conclusion never touches reads as decoration, even
  -- though the proof term passes through it.
  if specialist.isSome && !(← timed stats "dangling" (danglingHypotheses stmtClosed usedFVars.size)).isEmpty then
    stats.reject .danglingHypothesis
    return none

  let mut edges : Array (Nat × Nat × Name) := #[]
  for st in usedSteps do
    for parent in st.parentSteps do
      edges := edges.push (parent, st.stepIdx, st.lemmaName)
  let components : InterestComponents := {
    concepts
    modules := countDistinct (usedSteps.map fun st => definingModule env st.lemmaName)
    steps := usedSteps.size
    joins := shape.joins
    statementSize := exprSize stmtClosed
    readableSize := ← timed stats "readable_size" (visibleSize stmtClosed)
    focusSteps
  }
  return some {
    stmtClosed, proofClosed
    nBinders := usedFVars.size
    stepLabels := usedSteps.map fun st => (st.stepIdx, st.lemmaName, st.namespaceName)
    edges
    depth := shape.depths.back?.getD 0
    components
    score := interestScore components
    specialistSymbols
    stmtHash := canonicalHash stmtClosed
  }

/-- Insert into an array kept sorted by descending score and truncated to `cap`.
    A statement already present is not added again; on equal scores the earlier entry stays first. -/
def insertKept (kept : Array KeptDerivation) (k : KeptDerivation) (cap : Nat) : Array KeptDerivation :=
  if kept.any (·.stmtHash == k.stmtHash) then kept
  else
    let position := (kept.findIdx? (·.score < k.score)).getD kept.size
    (kept.insertIdx! position k).extract 0 cap

/-- Run the gates on a kept derivation, cheapest first: duplicate statement, rendering,
    kernel and axiom check, `exact?`, then `simp` and `aesop`. With `specialist` set, a
    statement closed by `simp` or `aesop` is rejected and the statement is rendered explicitly. -/
def gateKept
    (kept : KeptDerivation)
    (seed stepsRequested exactBudget aesopBudget convoluteDepth : Nat)
    (specialist : Bool)
    (seen : Std.HashSet String)
    (rng : Rng)
    (stats : StatsRef) : MetaM (Option WalkCandidate × Rng) := do
  if seen.contains kept.stmtHash then
    stats.reject .duplicateHash
    return (none, rng)

  let some (stmtDecl, stmtPretty, leanFile) ← timed stats "render" <|
    renderStandaloneClosed "akcm_candidate" kept.stmtClosed kept.proofClosed kept.nBinders
      kept.stepLabels convoluteDepth seed specialist
    | do
      stats.reject .unrenderable
      return (none, rng)

  -- Reopen the hypotheses to convolute the proof and recompute the invariants on the open terms.
  let (fullProof, rngConv, simpNormal, premiseReuse, conclusionSize) ←
    forallBoundedTelescope kept.stmtClosed (some kept.nBinders) fun xs concl => do
      let proofOpen := kept.proofClosed.beta xs
      let (convProof, rngConv) ←
        if convoluteDepth > 0 then convoluteExpr concl proofOpen convoluteDepth rng
        else pure (proofOpen, rng)
      let simpNormal := !(← isPaddedFact concl)
      let premiseReuse ← countPremiseReuse proofOpen
      return (← mkLambdaFVars xs convProof, rngConv, simpNormal, premiseReuse, exprSize concl)

  try
    check fullProof
  catch _ =>
    stats.reject .kernelCheck
    return (none, rngConv)

  let axs ← collectExprAxioms fullProof
  if !axiomsAreClean axs then
    stats.reject .badAxioms
    return (none, rngConv)

  let nov ← evaluateNovelty stats kept.stmtClosed fullProof exactBudget aesopBudget
  if !nov.level1ExactFailed then
    stats.reject .closedByExact
    return (none, rngConv)
  if specialist && !nov.level2NotRoutine then
    stats.reject (if nov.level2ClosedBy == some "simp" then .closedBySimp else .closedByAesop)
    return (none, rngConv)

  let mut nsArr : Array String := #[]
  for (_, _, ns) in kept.stepLabels do
    if !nsArr.contains ns then
      nsArr := nsArr.push ns

  let cand : WalkCandidate := {
    seed := seed
    stepsRequested := stepsRequested
    stepsTaken := kept.components.steps
    statementLean := stmtDecl
    statementPretty := stmtPretty
    statementHash := kept.stmtHash
    leanFile := leanFile
    axioms := axs.map Name.toString
    namespaces := nsArr
    depNodes := kept.stepLabels.map fun (stepIdx, lemma, ns) => (toString stepIdx, lemma.toString, ns)
    depEdges := kept.edges.map fun (parent, child, lemma) => (toString parent, toString child, lemma.toString)
    proofDepth := kept.depth
    proofJoins := kept.components.joins
    specialistSymbols := kept.specialistSymbols
    novelty := nov
    simpNormal := simpNormal
    premiseReuse := premiseReuse
    components := kept.components
    interestScore := kept.score
    conclusionSize := conclusionSize
  }
  return (some cand, rngConv)

/-- Finish a default (non-specialist) walk: close the derivation and gate it. -/
def finishWalk
    (stats : StatsRef)
    (seen : Std.HashSet String)
    (seed targetSteps exactBudget aesopBudget convoluteDepth : Nat)
    (ctxFVars : Array Expr)
    (steps : Array WalkStep)
    (rng : Rng) : MetaM (Option WalkCandidate × Rng) := do
  let some kept ← closeDerivation ctxFVars steps none stats | return (none, rng)
  gateKept kept seed targetSteps exactBudget aesopBudget convoluteDepth false seen rng stats

/-- Recursive driver executing steps `stepNum .. targetSteps` inside nested `withLocalDecl` scopes. -/
partial def runWalkLoop
    (stats : StatsRef)
    (limits : StepLimits)
    (seen : Std.HashSet String)
    (idx : LemmaIndex)
    (seed : Nat)
    (targetSteps : Nat)
    (interdiscWeight : Float)
    (exactBudget : Nat)
    (aesopBudget : Nat)
    (convoluteDepth : Nat)
    (ctxFVars : Array Expr)
    (steps : Array WalkStep)
    (addedHyps : Nat)
    (rng : Rng) : MetaM (Option WalkCandidate × Rng) := do
  if steps.size >= targetSteps then
    return ← finishWalk stats seen seed targetSteps exactBudget aesopBudget convoluteDepth ctxFVars steps rng

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
      return ← runWalkLoop stats limits seen idx seed steps.size interdiscWeight exactBudget aesopBudget convoluteDepth ctxFVars steps addedHyps r
    else
      return (none, r)

  let cands := idx.byHypHead.getD headName #[]
  if cands.isEmpty then
    if steps.size >= 3 then
      return ← runWalkLoop stats limits seen idx seed steps.size interdiscWeight exactBudget aesopBudget convoluteDepth ctxFVars steps addedHyps r
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
    let (resOpt, r'') ← tryApplyLemma stats limits candName targetStep steps ctxFVars addedHyps steps.size r
    r := r''
    match resOpt with
    | none =>
        restoreState saved
    | some (binderSpecs, mkStep) =>
        let stepRes ← withOpenedBinders stats binderSpecs.toList #[] fun freshFVars => do
          match ← mkStep freshFVars with
          | none => return none
          | some newStep =>
              let (finalOpt, _) ← runWalkLoop
                stats limits seen idx seed targetSteps interdiscWeight exactBudget aesopBudget convoluteDepth
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
    runWalkLoop stats limits seen idx seed steps.size interdiscWeight exactBudget aesopBudget convoluteDepth ctxFVars steps addedHyps r
  else
    return (none, r)

def buildHypothesisTree (idx : LemmaIndex) : MetaM (DiscrTree Name) := do
  let env ← getEnv
  let mut tree : DiscrTree Name := {}
  -- Always index all specialist lemmas first, then up to 12,000 ambient lemmas
  let mut seen : NameSet := {}
  let mut toIndex : Array Name := #[]
  for l in idx.specialistSeeds do
    if !seen.contains l then
      seen := seen.insert l
      toIndex := toIndex.push l
  let ambientCap : Nat := 12000
  let mut ambientAdded : Nat := 0
  for l in idx.indexedLemmas do
    if ambientAdded >= ambientCap then break
    if !seen.contains l then
      seen := seen.insert l
      toIndex := toIndex.push l
      ambientAdded := ambientAdded + 1
  for lemma in toIndex do
    let some (.thmInfo info) := env.find? lemma | continue
    let keys ← tryCatchRuntimeEx (withHeartbeatBudget 25000 do
        withReducible do
          withNewMCtxDepth do
            let (args, binderInfos, _) ← forallMetaTelescope
              (info.instantiateTypeLevelParams (concreteLevels info))
            let mut keys := #[]
            for i in [:args.size] do
              if binderInfos[i]! == .default then
                let type ← inferType args[i]!
                if ← isProp type then
                  keys := keys.push (← DiscrTree.mkPath type)
            return keys) (fun _ => pure #[])
    for key in keys do
      if key.size > 1 || key[0]? != some DiscrTree.Key.star then
        tree := tree.insertKeyValue key lemma
  return tree

def recordProgress (progress : IO.Ref SpecialistProgress) (shape : ProofShape) : MetaM Unit := do
  let depth := shape.depths.back?.getD 0
  progress.modify fun previous => {
    maxDepth := max previous.maxDepth depth
    maxJoinedDepth := if shape.joins == 0 then previous.maxJoinedDepth
      else max previous.maxJoinedDepth depth
  }

def joinCandidates (idx : LemmaIndex) (shape : ProofShape) (matchedLemmas : Array (Array Name)) :
    Array (Nat × Name) := Id.run do
  let latest := matchedLemmas.size - 1
  let previous := matchedLemmas.map fun lemmas =>
    lemmas.foldl (init := ({} : NameSet)) fun acc lemma => acc.insert lemma
  let mut candidates := #[]
  for lemma in matchedLemmas.back?.getD #[] do
    if !idx.multiPremiseLemmas.contains lemma then continue
    for i in [:latest] do
      if !(shape.ancestors[latest]!).contains i && previous[i]!.contains lemma then
        candidates := candidates.push (latest, lemma)
        break
  return candidates

/-- Draw up to four lemmas and take the first whose conclusion is about a concept the
    derivation has not touched yet; otherwise the first drawn. -/
def pickPreferringNewConcept (idx : LemmaIndex) (pool : Array Name) (usedConcepts : Array Name)
    (rng : Rng) : Option Name × Rng := Id.run do
  let mut r := rng
  let mut first : Option Name := none
  for _ in [:4] do
    let (drawn?, r') := r.pickArray? pool
    r := r'
    let some drawn := drawn? | break
    if first.isNone then
      first := some drawn
    match idx.conclHead.get? drawn with
    | some head => if !usedConcepts.contains head then return (some drawn, r)
    | none => pure ()
  return (first, r)

/-- Depth-first specialist search. It spends the whole trial budget of the walk and records
    every derivation that qualifies in `kept` (best `search.keep` by interest score).
    No gate runs here; `runSingleWalk` gates the kept derivations afterwards. -/
partial def runSpecialistLoop
    (stats : StatsRef)
    (idx : LemmaIndex)
    (hypotheses : DiscrTree Name)
    (search : SpecialistSearch)
    (progress : IO.Ref SpecialistProgress)
    (remaining : IO.Ref Nat)
    (kept : IO.Ref (Array KeptDerivation))
    (maxSteps : Nat)
    (ctxFVars : Array Expr)
    (steps : Array WalkStep)
    (priorMatches : Array (Array Name))
    (addedHyps : Nat)
    (rng : Rng) : MetaM Unit := do
  let shape := proofShape steps
  recordProgress progress shape
  if let some derivation ← closeDerivation ctxFVars steps (some search) stats then
    kept.modify (insertKept · derivation search.keep)
  if steps.size >= maxSteps then return

  let latestMatches ← tryCatchRuntimeEx
    (hypotheses.getMatch steps.back!.factType) (fun _ => pure #[])
  let matchedLemmas := priorMatches.push latestMatches
  let joins := if shape.joins == 0 then joinCandidates idx shape matchedLemmas else #[]
  let usedConcepts := steps.filterMap (·.concept)
  -- Until the derivation has its on-topic steps, most extensions draw from focus lemmas.
  let env ← getEnv
  let isFocus := fun (lemma : Name) => (definingModule env lemma).any search.focus.isPrefixOf
  let needsFocus := (steps.countP fun st => isFocus st.lemmaName) < search.minFocusSteps
  let mut r := rng
  let mut tried : Std.HashSet (Nat × Name) := {}
  -- Each node extends at most three ways, so the budget is not spent on one tip.
  let mut children := 0
  for attempt in [:40] do
    if children >= 3 then break
    let left ← remaining.get
    if left == 0 then return
    let (choice, nextRng) := if attempt % 4 == 0 && !joins.isEmpty then
      r.pickArray? joins
    else
      -- Extend the tip for length, and periodically fork an earlier part of the derivation.
      let (earlier, r) := r.nextNat (steps.size - 1)
      let source := if attempt % 5 < 3 then steps.size - 1 else earlier
      let precise := matchedLemmas[source]!
      let fallback := (steps[source]!.factType.getAppFn.constName?).map (fun head =>
        let focused := idx.bySpecialistHypHead.getD head #[]
        if attempt % 2 == 0 && !focused.isEmpty then focused else idx.byHypHead.getD head #[])
      let pool := if attempt % 5 < 4 && !precise.isEmpty then precise else fallback.getD #[]
      let pool := if needsFocus && attempt % 4 != 3 then preferFocus pool isFocus else pool
      let (candidate, r) := pickPreferringNewConcept idx pool usedConcepts r
      (candidate.map (source, ·), r)
    r := nextRng
    let some (source, lemma) := choice | continue
    let target := steps[source]!
    if lemma == target.lemmaName || tried.contains (target.stepIdx, lemma) then continue
    tried := tried.insert (target.stepIdx, lemma)
    remaining.set (left - 1)
    let saved ← saveState
    let extended ← tryCatchRuntimeEx (do
      let (result, nextRng) ← withHeartbeatBudget 40000 do
        tryApplyLemma stats search.limits lemma target steps.reverse ctxFVars addedHyps steps.size r
      match result with
      | none => pure false
      | some (binderSpecs, mkStep) =>
        let deeper ← withOpenedBinders stats binderSpecs.toList #[] fun freshFVars => do
          let step ← withHeartbeatBudget 40000 do
            mkStep freshFVars
          let some step := step | return none
          runSpecialistLoop stats idx hypotheses search progress remaining kept maxSteps
            (ctxFVars ++ freshFVars) (steps.push step) matchedLemmas
            (addedHyps + freshFVars.size) nextRng
          return some ()
        pure deeper.isSome)
      (fun _ => do stats.reject .heartbeat; pure false)
    if extended then
      children := children + 1
    restoreState saved

/-- Start a single random forward walk from a random Mathlib seed theorem. -/
def runSingleWalk
    (stats : StatsRef)
    (limits : StepLimits)
    (seen : Std.HashSet String)
    (idx : LemmaIndex)
    (seed : Nat)
    (minSteps maxSteps : Nat)
    (interdiscWeight : Float)
    (exactBudget aesopBudget convoluteDepth : Nat)
    (rng : Rng)
    (specialist : Option (SpecialistSearch × DiscrTree Name × IO.Ref SpecialistProgress) := none) :
    MetaM (Option WalkCandidate × Rng) := do
  let seeds := if specialist.isSome then idx.specialistSeeds else idx.seeds
  let (seedNameOpt, r1) := rng.pickArray? seeds
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
      concept := conceptOf concl
    }
    if let some (search, hypotheses, progress) := specialist then
      let (walkRng, nextRng) := r2.nextUInt64
      let remaining ← IO.mkRef search.trialsPerWalk
      let kept ← IO.mkRef (#[] : Array KeptDerivation)
      runSpecialistLoop stats idx hypotheses search progress remaining kept maxSteps
        fvars #[step0] #[] 0 { state := walkRng }
      -- Gate the best derivations of this walk, best first, until one passes.
      let mut gateRng := nextRng
      for derivation in (← kept.get) do
        let (candidate, r') ← tryCatchRuntimeEx
          (gateKept derivation seed maxSteps exactBudget aesopBudget convoluteDepth true seen gateRng stats)
          (fun _ => do stats.reject .heartbeat; pure (none, gateRng))
        gateRng := r'
        if candidate.isSome then
          return (candidate, gateRng)
      return (none, gateRng)
    runWalkLoop stats limits seen idx seed targetSteps interdiscWeight exactBudget aesopBudget convoluteDepth fvars #[step0] 0 r2

end Babel
