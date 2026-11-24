import Lean
import Babel

open Lean Meta Babel

structure CliConfig where
  seed : Nat := 20261124
  count : Nat := 10
  minSteps : Nat := 3
  maxSteps : Nat := 8
  maxAttempts : Nat := 400
  interdisciplinary : Float := 2.0
  exactHeartbeats : Nat := 150000
  aesopHeartbeats : Nat := 150000
  convolute : Nat := 3
  importModule : Name := `Babel.Corpus
  focus : Option Name := none
  minProofDepth : Nat := 8
  trialsPerWalk : Nat := 240
  outPath : String := ".tmp/walk_out.json"

def parseFloatArg (s : String) (fallback : Float) : Float :=
  let parts := s.splitOn "."
  match parts with
  | [a] => match a.toNat? with | some n => Float.ofNat n | none => fallback
  | [a, b] =>
      match a.toNat?, b.toNat? with
      | some na, some nb =>
          let denom := Float.pow 10.0 (Float.ofNat b.length)
          Float.ofNat na + Float.ofNat nb / denom
      | _, _ => fallback
  | _ => fallback

partial def parseArgs (args : List String) (cfg : CliConfig := {}) : CliConfig :=
  match args with
  | "--seed" :: v :: rest =>
      parseArgs rest { cfg with seed := v.toNat?.getD cfg.seed }
  | "--count" :: v :: rest =>
      parseArgs rest { cfg with count := v.toNat?.getD cfg.count }
  | "--steps" :: v :: rest =>
      let k := v.toNat?.getD cfg.minSteps
      parseArgs rest { cfg with minSteps := k, maxSteps := k }
  | "--min-steps" :: v :: rest =>
      parseArgs rest { cfg with minSteps := v.toNat?.getD cfg.minSteps }
  | "--max-steps" :: v :: rest =>
      parseArgs rest { cfg with maxSteps := v.toNat?.getD cfg.maxSteps }
  | "--max-attempts" :: v :: rest =>
      parseArgs rest { cfg with maxAttempts := v.toNat?.getD cfg.maxAttempts }
  | "--interdisciplinary" :: v :: rest =>
      parseArgs rest { cfg with interdisciplinary := parseFloatArg v cfg.interdisciplinary }
  | "--exact-heartbeats" :: v :: rest =>
      parseArgs rest { cfg with exactHeartbeats := v.toNat?.getD cfg.exactHeartbeats }
  | "--aesop-heartbeats" :: v :: rest =>
      parseArgs rest { cfg with aesopHeartbeats := v.toNat?.getD cfg.aesopHeartbeats }
  | "--convolute" :: v :: rest =>
      parseArgs rest { cfg with convolute := v.toNat?.getD cfg.convolute }
  | "--module" :: v :: rest =>
      parseArgs rest { cfg with importModule := v.toName }
  | "--focus" :: v :: rest =>
      parseArgs rest { cfg with focus := some v.toName }
  | "--min-proof-depth" :: v :: rest =>
      parseArgs rest { cfg with minProofDepth := v.toNat?.getD cfg.minProofDepth }
  | "--trials-per-walk" :: v :: rest =>
      parseArgs rest { cfg with trialsPerWalk := v.toNat?.getD cfg.trialsPerWalk }
  | "--out" :: v :: rest =>
      parseArgs rest { cfg with outPath := v }
  | _ :: rest => parseArgs rest cfg
  | [] => cfg

def floatToJson (x : Float) : Json :=
  -- Round to 2 decimal places as JSON number
  match JsonNumber.fromFloat? ((x * 100.0).round / 100.0) with
  | .inr jn => Json.num jn
  | .inl _ => Json.num 0

def candidateToJson (c : WalkCandidate) : Json :=
  let nodesJson := c.depNodes.map fun (id, lemma, ns) =>
    Json.mkObj [("id", Json.str id), ("lemma", Json.str lemma), ("namespace", Json.str ns),
      ("kind", Json.str "mathlib")]
  let edgesJson := c.depEdges.map fun (src, dst, lbl) =>
    Json.mkObj [("from", Json.str src), ("to", Json.str dst), ("lemma", Json.str lbl),
      ("step", Json.str s!"step_{dst}")]
  let shape := Json.mkObj [
    ("depth", toJson c.proofDepth),
    ("joins", toJson c.proofJoins),
    ("specialist_symbols", toJson (c.specialistSymbols.map Name.toString))
  ]
  let novJson := Json.mkObj [
    ("level_0_unseen", Json.bool c.novelty.level0Unseen),
    ("level_1_exact_failed", Json.bool c.novelty.level1ExactFailed),
    ("level_1_budget_heartbeats", Json.num c.novelty.level1BudgetHeartbeats),
    ("level_2_not_routine", Json.bool c.novelty.level2NotRoutine),
    ("level_2_closed_by", match c.novelty.level2ClosedBy with | some s => Json.str s | none => Json.null),
    ("level_3_proof_size", Json.num c.novelty.level3ProofSize),
    ("level_3_statement_size", Json.num c.novelty.level3StatementSize),
    ("level_3_ratio", floatToJson c.novelty.level3Ratio)
  ]
  Json.mkObj [
    ("seed", Json.num c.seed),
    ("steps_requested", Json.num c.stepsRequested),
    ("steps_taken", Json.num c.stepsTaken),
    ("statement_lean", Json.str c.statementLean),
    ("statement_pretty", Json.str c.statementPretty),
    ("statement_hash", Json.str c.statementHash),
    ("lean_file", Json.str c.leanFile),
    ("axioms", Json.arr (c.axioms.map Json.str)),
    ("namespaces", Json.arr (c.namespaces.map Json.str)),
    ("dependencies", Json.mkObj [("nodes", Json.arr nodesJson), ("edges", Json.arr edgesJson)]),
    ("proof_shape", shape),
    ("novelty", novJson)
  ]

unsafe def main (args : List String) : IO Unit := do
  let cfg := parseArgs args
  let specialist : Option SpecialistSearch := cfg.focus.map fun focus =>
    { focus, minProofDepth := cfg.minProofDepth, trialsPerWalk := cfg.trialsPerWalk }
  if specialist.isSome && (cfg.minProofDepth < 3 || cfg.maxSteps <= cfg.minProofDepth) then
    throw <| IO.userError "Specialist search requires 3 <= --min-proof-depth < --max-steps."
  IO.eprintln s!"[Babel.walk] Loading {cfg.importModule}..."
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := cfg.importModule }] {} (loadExts := true)
  IO.eprintln s!"[Babel.walk] Building Mathlib lemma index..."
  let idx := buildLemmaIndex env cfg.focus
  IO.eprintln s!"[Babel.walk] Indexed {idx.totalIndexed} theorems, {idx.seeds.size} seeds, {idx.byHypHead.size} head symbols."
  if let some search := specialist then
    if idx.specialistSeeds.isEmpty then
      throw <| IO.userError s!"No seeds from {search.focus} are available in {cfg.importModule}."
    IO.eprintln s!"[Babel.walk] Using {idx.specialistSeeds.size} specialist seeds from {search.focus}."

  let coreCtx : Core.Context := {
    fileName := "<babel-walk>"
    fileMap := default
    maxHeartbeats := 0
    maxRecDepth := if specialist.isSome then 3500 else 1000
  }
  let coreState : Core.State := { env := env }
  let progress ← IO.mkRef ({} : SpecialistProgress)

  let action : MetaM (Array WalkCandidate) := do
    let specialistContext ← specialist.mapM fun search => do
      IO.eprintln "[Babel.walk] Indexing normalized hypothesis patterns."
      return (search, ← buildHypothesisTree idx, progress)
    let mut rng := Rng.ofSeed cfg.seed
    let mut accepted : Array WalkCandidate := #[]
    let mut seenHashes : Std.HashSet String := {}
    let mut attempts := 0

    while accepted.size < cfg.count && attempts < cfg.maxAttempts do
      attempts := attempts + 1
      let walkSeed := cfg.seed + attempts * 1009
      let walk := runSingleWalk idx walkSeed cfg.minSteps cfg.maxSteps cfg.interdisciplinary
        cfg.exactHeartbeats cfg.aesopHeartbeats cfg.convolute rng
        specialistContext
      let (candOpt, rng') ← if specialist.isSome then
        tryCatchRuntimeEx walk (fun _ => pure (none, (rng.nextUInt64).2))
      else walk
      rng := rng'
      if let some cand := candOpt then
        if !seenHashes.contains cand.statementHash then
          seenHashes := seenHashes.insert cand.statementHash
          accepted := accepted.push cand
          IO.eprintln s!"[Babel.walk] #{accepted.size}/{cfg.count} (attempt {attempts}): steps={cand.stepsTaken}, depth={cand.proofDepth}, joins={cand.proofJoins}, L2_not_routine={cand.novelty.level2NotRoutine}, L3_ratio={cand.novelty.level3Ratio}, ns={cand.namespaces}"
    IO.eprintln s!"[Babel.walk] Completed {attempts} attempts."
    if specialist.isSome then
      let stats ← progress.get
      IO.eprintln s!"[Babel.walk] Max depth: {stats.maxDepth}; max depth with a branch join: {stats.maxJoinedDepth}."
    return accepted

  let (candidates, _) ← (action.run' {} {}).toIO coreCtx coreState
  let jsonOut := Json.arr (candidates.map candidateToJson)
  let outFile := System.FilePath.mk cfg.outPath
  if let some parent := outFile.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outFile (jsonOut.pretty ++ "\n")
  IO.eprintln s!"[Babel.walk] Wrote {candidates.size} gated candidates to {cfg.outPath}."
