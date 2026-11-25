import Babel.Generator
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Continuous
import Mathlib.Logic.Function.Const
import Mathlib.AlgebraicTopology.SimplicialObject.Split
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
Builds the referee calibration set: real Mathlib theorems printed the way the generator
prints its own statements, so that the referees can be asked to score them through the
same prompt. The output is committed as `scripts/calibration_set.json`.

    lake env lean scripts/calibration_set.lean > scripts/calibration_set.json

Three tiers. `famous` and `trivial` are chosen by hand and anchor the two ends of the
scale. `library` is a seeded random sample of the theorems of modules the specialist search
has explored, and needs no judgment. It includes equivalences, equations and generated
projection lemmas, which the search itself never starts from.
-/

open Lean Meta Babel

namespace Calibration

def famous : Array Name := #[
  ``Nat.exists_infinite_primes,
  ``Subgroup.card_subgroup_dvd_card,
  ``Function.cantor_surjective,
  ``intermediate_value_Icc,
  ``IsCompact.exists_isMinOn,
  ``Matrix.aeval_self_charpoly,
  ``Complex.exists_root,
  ``Sylow.exists_subgroup_card_pow_prime,
  ``ContractingWith.exists_fixedPoint,
  ``Metric.isCompact_iff_isClosed_bounded,
  ``ZMod.pow_card_sub_one_eq_one,
  ``Nat.sum_four_squares,
  ``exists_deriv_eq_slope,
  ``irrational_sqrt_two,
  ``IsGalois.card_aut_eq_finrank,
  ``Ideal.exists_le_maximal,
  ``Function.Embedding.schroeder_bernstein,
  ``LinearMap.finrank_range_add_finrank_ker
]

def trivial : Array Name := #[
  ``Set.inter_comm,
  ``Set.subset_union_left,
  ``Set.Subset.refl,
  ``Set.union_self,
  ``Finset.inter_comm,
  ``Finset.card_empty,
  ``continuous_id,
  ``le_refl
]

def sampledModules : Array Name := #[
  `Mathlib.Logic.Function.Const,
  `Mathlib.AlgebraicTopology.SimplicialObject.Split,
  `Mathlib.RingTheory.PowerSeries.Substitution,
  `Mathlib.FieldTheory.Galois.Basic,
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact,
  `Mathlib.Order.Filter.Basic,
  `Mathlib.RingTheory.Localization.Ideal,
  `Mathlib.Topology.Sheaves.MayerVietoris
]

def samplesPerModule : Nat := 3
def sampleSeed : Nat := 20261125
/-- The generator's cap on a statement (`StepLimits.maxFactSize`). -/
def maxStatementSize : Nat := 400
def proofSizeCap : Nat := 5000000

/-- Node count of a term, counted like `exprSize` and stopped at `cap`: the proof of a
    named theorem can be very large once sharing is expanded. -/
partial def cappedSize (cap : Nat) (e : Expr) : StateM Nat Unit := do
  if (← get) ≥ cap then return
  match e with
  | .app f a => modify (· + 1); cappedSize cap f; cappedSize cap a
  | .lam _ t b _ => modify (· + 1); cappedSize cap t; cappedSize cap b
  | .forallE _ t b _ => modify (· + 1); cappedSize cap t; cappedSize cap b
  | .letE _ t v b _ => modify (· + 1); cappedSize cap t; cappedSize cap v; cappedSize cap b
  | .mdata _ inner => cappedSize cap inner
  | .proj _ _ inner => modify (· + 1); cappedSize cap inner
  | _ => modify (· + 1)

/-- Mathlib theorems cited by the proof of `root`, in order of first use. Auxiliary and
    private declarations are opened, since nobody could cite them by name. Instances that
    happen to be theorems are left out: the generator's lemma lists never contain one. -/
partial def citedTheorems (env : Environment) (root : Name) : Array Name :=
  let rec visit (decl : Name) : StateM (NameSet × Array Name) Unit := do
    let some info := env.find? decl | return
    let some value := info.value? (allowOpaque := true) | return
    for used in value.getUsedConstants do
      if (← get).1.contains used then continue
      modify fun (seen, out) => (seen.insert used, out)
      match env.find? used with
      | some (.thmInfo _) =>
          if used.isInternalDetail || root.isPrefixOf used then
            visit used
          else if (definingModule env used).any (`Mathlib).isPrefixOf && isCleanMathlibName used
              && !isInstanceCore env used then
            modify fun (seen, out) => (seen, out.push used)
      | _ => pure ()
  ((visit root).run ({}, #[])).2.2

/-- The statement as `renderStandaloneClosed` prints the readable form. -/
def prettyStatement (type : Expr) : MetaM String := do
  let fmt ← withOptions (fun o =>
      o.set `pp.unicode.fun true
      |>.set `pp.universes false
      |>.set `pp.explicit false) do
    ppExpr type
  return fmt.pretty 92

def printable (text : String) : Bool :=
  (text.splitOn "⋯").length == 1 && (text.splitOn "✝").length == 1

def describe (tier : String) (name : Name) : MetaM (Option Json) := do
  let env ← getEnv
  let .thmInfo info ← getConstInfo name | throwError "{name} is not a theorem"
  let type := info.instantiateTypeLevelParams (concreteLevels info)
  let statement ← prettyStatement type
  if !printable statement then return none
  let lemmas := citedTheorems env name
  let (_, proofSize) := (cappedSize proofSizeCap info.value).run 0
  let simpLemma := (← getSimpTheorems).isLemma (.decl name)
  return some <| Json.mkObj [
    ("tier", Json.str tier),
    ("name", Json.str name.toString),
    ("module", Json.str ((definingModule env name).map Name.toString |>.getD "")),
    ("statement_pretty", Json.str statement),
    ("lemmas", Json.arr (lemmas.map fun l => Json.str l.toString)),
    ("statement_size", Json.num (exprSize type)),
    ("proof_size", Json.num proofSize),
    ("simp", Json.bool simpLemma)
  ]

/-- The theorems of one module with a citable name, sorted by name. -/
def moduleTheorems (env : Environment) (module : Name) : Array Name :=
  let names := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc name info =>
    match info with
    | .thmInfo _ =>
        if definingModule env name == some module && isCleanMathlibName name
            && !Linter.isDeprecated env name then acc.push name
        else acc
    | _ => acc
  names.qsort fun a b => a.toString < b.toString

def shuffle (names : Array Name) (rng : Rng) : Array Name × Rng := Id.run do
  let mut out := names
  let mut rng := rng
  for i in [:out.size] do
    let (offset, next) := rng.nextNat (out.size - i)
    rng := next
    let j := i + offset
    let tmp := out[i]!
    out := out.set! i out[j]!
    out := out.set! j tmp
  return (out, rng)

def build : MetaM Json := do
  let env ← getEnv
  let mut items : Array Json := #[]
  for name in famous do
    let some item ← describe "famous" name | throwError "{name} does not print cleanly"
    items := items.push item
  for name in trivial do
    let some item ← describe "trivial" name | throwError "{name} does not print cleanly"
    items := items.push item
  let mut rng := Rng.ofSeed sampleSeed
  for module in sampledModules do
    let (order, next) := shuffle (moduleTheorems env module) rng
    rng := next
    let mut taken := 0
    for name in order do
      if taken == samplesPerModule then break
      let .thmInfo info ← getConstInfo name | continue
      if exprSize info.type > maxStatementSize then continue
      let some item ← describe "library" name | continue
      items := items.push item
      taken := taken + 1
    if taken < samplesPerModule then
      throwError "{module} has fewer than {samplesPerModule} printable theorems"
  return Json.mkObj [
    ("mathlib_rev", Json.str "v4.36.0"),
    ("sample_seed", Json.num sampleSeed),
    ("items", Json.arr items)
  ]

end Calibration

#eval show MetaM Unit from do
  IO.println (← Calibration.build).pretty
