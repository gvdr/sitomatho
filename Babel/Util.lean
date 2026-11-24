import Lean

namespace Babel

open Lean Meta

/-- Deterministic SplitMix64 PRNG for reproducible theorem walks. -/
structure Rng where
  state : UInt64
deriving Inhabited

namespace Rng

def ofSeed (seed : Nat) : Rng :=
  { state := UInt64.ofNat (seed + 0x9e3779b97f4a7c15) }

def nextUInt64 (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  let z := z ^^^ (z >>> 31)
  (z, { state := s })

def nextNat (r : Rng) (bound : Nat) : Nat × Rng :=
  if bound <= 1 then (0, r)
  else
    let (v, r') := r.nextUInt64
    (v.toNat % bound, r')

def nextRange (r : Rng) (lo hi : Nat) : Nat × Rng :=
  if hi <= lo then (lo, r)
  else
    let (d, r') := r.nextNat (hi - lo + 1)
    (lo + d, r')

def nextFloat (r : Rng) : Float × Rng :=
  let (v, r') := r.nextUInt64
  -- Use top 53 bits for uniform [0, 1)
  let top := (v >>> 11).toNat
  (Float.ofNat top / 9007199254740992.0, r')

def pickArray? {α : Type} (r : Rng) (arr : Array α) : Option α × Rng :=
  if arr.isEmpty then (none, r)
  else
    let (idx, r') := r.nextNat arr.size
    (arr[idx]?, r')

end Rng

/-- Count AST nodes in a Lean expression (used for Level 3 proof/statement depth ratio). -/
partial def exprSize : Expr → Nat
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ t b _ => 1 + exprSize t + exprSize b
  | .forallE _ t b _ => 1 + exprSize t + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e => exprSize e
  | .proj _ _ e => 1 + exprSize e
  | _ => 1

/-- Alpha-invariant hash of a closed Lean expression (ignores binder names & binder info). -/
partial def canonicalHashCore (e : Expr) (acc : UInt64) : UInt64 :=
  let mix (a b : UInt64) : UInt64 := (a * 1099511628211) ^^^ b
  match e with
  | .bvar i => mix acc (0x101 ^^^ UInt64.ofNat i)
  | .fvar id => mix acc (0x102 ^^^ hash id.name)
  | .mvar id => mix acc (0x103 ^^^ hash id.name)
  | .sort l => mix acc (0x104 ^^^ hash l)
  | .const n ls =>
      let h := mix acc (0x105 ^^^ hash n)
      ls.foldl (fun a l => mix a (hash l)) h
  | .app f a =>
      let h := canonicalHashCore f (mix acc 0x106)
      canonicalHashCore a h
  | .lam _ t b _ =>
      let h := canonicalHashCore t (mix acc 0x107)
      canonicalHashCore b h
  | .forallE _ t b _ =>
      let h := canonicalHashCore t (mix acc 0x108)
      canonicalHashCore b h
  | .letE _ t v b _ =>
      let h := canonicalHashCore t (mix acc 0x109)
      let h := canonicalHashCore v h
      canonicalHashCore b h
  | .lit l => mix acc (0x10a ^^^ hash l)
  | .mdata _ inner => canonicalHashCore inner acc
  | .proj s i inner => canonicalHashCore inner (mix (mix acc (0x10b ^^^ hash s)) (UInt64.ofNat i))

def hexOfUInt64 (x : UInt64) : String :=
  let digits := "0123456789abcdef".toList.toArray
  Id.run do
    let mut s := ""
    let mut v := x
    for _ in [:16] do
      let nib := ((v >>> 60) &&& 0xf).toNat
      s := s.push (digits[nib]!)
      v := v <<< 4
    return s

def canonicalHash (e : Expr) : String :=
  let h1 := canonicalHashCore e 14695981039346656037
  let h2 := canonicalHashCore e 0x9e3779b97f4a7c15
  s!"expr:{hexOfUInt64 h1}{hexOfUInt64 h2}"

/-- Extract a readable top-level Mathlib namespace from a declaration name. -/
def topNamespace (n : Name) : String :=
  let comps := n.components
  match comps with
  | [] => "Core"
  | [c] => c.toString
  | c1 :: c2 :: _ =>
      let s1 := c1.toString
      if s1 == "Mathlib" || s1 == "Batteries" || s1 == "Std" then c2.toString
      else s1

/-- Collect all constant names referenced in an expression. -/
def collectConsts (e : Expr) : NameSet :=
  e.foldConsts NameSet.empty (fun c s => s.insert c)

/-- Collect all FVarIds appearing in an expression. -/
partial def collectFVarsExpr (e : Expr) (acc : FVarIdSet := {}) : FVarIdSet :=
  if !e.hasFVar then acc
  else match e with
  | .fvar id => acc.insert id
  | .app f a => collectFVarsExpr a (collectFVarsExpr f acc)
  | .lam _ t b _ => collectFVarsExpr b (collectFVarsExpr t acc)
  | .forallE _ t b _ => collectFVarsExpr b (collectFVarsExpr t acc)
  | .letE _ t v b _ => collectFVarsExpr b (collectFVarsExpr v (collectFVarsExpr t acc))
  | .mdata _ inner => collectFVarsExpr inner acc
  | .proj _ _ inner => collectFVarsExpr inner acc
  | _ => acc

/-- Transitive closure of FVarIds required by `seed` within the current local context. -/
def closeFVarsTransitively (seed : FVarIdSet) : MetaM FVarIdSet := do
  let mut kept := seed
  let mut queue := seed.toList
  while !queue.isEmpty do
    match queue with
    | [] => break
    | fid :: rest =>
        queue := rest
        if let some decl := (← getLCtx).find? fid then
          let deps := collectFVarsExpr decl.type
          let deps := match decl.value? with
            | some v => collectFVarsExpr v deps
            | none => deps
          for d in deps do
            if !kept.contains d then
              kept := kept.insert d
              queue := d :: queue
  return kept

/-- Check whether an axiom list contains only standard Lean axioms. -/
def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

def axiomsAreClean (axs : Array Name) : Bool :=
  axs.all fun a => allowedAxioms.contains a

/-- Collect all axioms transitively used by an expression via the environment. -/
partial def collectExprAxioms (e : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut queue : List Name := (collectConsts e).toList
  while !queue.isEmpty do
    match queue with
    | [] => break
    | c :: rest =>
        queue := rest
        if visited.contains c then continue
        visited := visited.insert c
        match env.find? c with
        | some (.axiomInfo _) =>
            axioms := axioms.insert c
        | some info =>
            if let some val := info.value? then
              for d in collectConsts val do
                if !visited.contains d then
                  queue := d :: queue
            for d in collectConsts info.type do
              if !visited.contains d then
                queue := d :: queue
        | none => pure ()
  return axioms.toList.toArray

end Babel
