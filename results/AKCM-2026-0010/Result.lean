import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.OrderDual

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: SimpleGraph.fromEdgeSet_mono (SimpleGraph)
-- Step 7: isLUB_Icc (isLUB_Icc)
-- Step 10: IsLUB.insert (IsLUB)
-- Step 11: IsLUB.dual (IsLUB)
-- Step 12: IsGLB.isGLB_sInf (IsGLB)
-- Step 13: IsGLB.unique (IsGLB)
theorem akcm_2026_0010
    {V : Type}
    {s : Set.{0} (Sym2.{0} V)}
    {t : Set.{0} (Sym2.{0} V)}
    (h : @LE.le.{0} (Set.{0} (Sym2.{0} V)) (@Set.instLE.{0} (Sym2.{0} V)) s t)
    {u : SimpleGraph.{0} V} :
    @Eq.{1} (OrderDual.{0} (SimpleGraph.{0} V))
  (@sInf.{0} (OrderDual.{0} (SimpleGraph.{0} V))
    (@OrderInfSet.toInfSet.{0} (OrderDual.{0} (SimpleGraph.{0} V))
      (@Preorder.toLE.{0} (OrderDual.{0} (SimpleGraph.{0} V))
        (@OrderDual.instPreorder.{0} (SimpleGraph.{0} V)
          (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
            (@SimpleGraph.instPartialOrder.{0} V))))
      (@OrderDual.orderInfSet.{0} (SimpleGraph.{0} V)
        (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
          (@SimpleGraph.instPartialOrder.{0} V))
        (@CompleteSemilatticeSup.toOrderSupSet.{0} (SimpleGraph.{0} V)
          (@CompleteLattice.toCompleteSemilatticeSup.{0} (SimpleGraph.{0} V)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                (SimpleGraph.{0} V)
                (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V)))))))
    (@Set.preimage.{0, 0} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
      (@DFunLike.coe.{1, 1, 1}
        (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
        (OrderDual.{0} (SimpleGraph.{0} V)) (fun x ↦ SimpleGraph.{0} V)
        (@EquivLike.toFunLike.{1, 1, 1}
          (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
          (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
          (@Equiv.instEquivLike.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V))
            (SimpleGraph.{0} V)))
        (@OrderDual.ofDual.{0} (SimpleGraph.{0} V)))
      (@insert.{0, 0} (SimpleGraph.{0} V) (Set.{0} (SimpleGraph.{0} V))
        (@Set.instInsert.{0} (SimpleGraph.{0} V)) u
        (@Set.Icc.{0} (SimpleGraph.{0} V)
          (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
            (@SimpleGraph.instPartialOrder.{0} V))
          (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t)))))
  (@DFunLike.coe.{1, 1, 1}
    (Equiv.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V)))
    (SimpleGraph.{0} V) (fun x ↦ OrderDual.{0} (SimpleGraph.{0} V))
    (@EquivLike.toFunLike.{1, 1, 1}
      (Equiv.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V)))
      (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V))
      (@Equiv.instEquivLike.{1, 1} (SimpleGraph.{0} V)
        (OrderDual.{0} (SimpleGraph.{0} V))))
    (@OrderDual.toDual.{0} (SimpleGraph.{0} V))
    (@max.{0} (SimpleGraph.{0} V)
      (@SemilatticeSup.toMax.{0} (SimpleGraph.{0} V)
        (@Lattice.toSemilatticeSup.{0} (SimpleGraph.{0} V)
          (@CompleteLattice.toLattice.{0} (SimpleGraph.{0} V)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                (SimpleGraph.{0} V)
                (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V))))))
      u (@SimpleGraph.fromEdgeSet.{0} V t))) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @IsGLB.unique.{0} (OrderDual.{0} (SimpleGraph.{0} V))
      (@OrderDual.instPartialOrder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
      (@Set.preimage.{0, 0} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
        (@DFunLike.coe.{1, 1, 1}
          (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
          (OrderDual.{0} (SimpleGraph.{0} V)) (fun x ↦ SimpleGraph.{0} V)
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
            (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
            (@Equiv.instEquivLike.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)))
          (@OrderDual.ofDual.{0} (SimpleGraph.{0} V)))
        (@insert.{0, 0} (SimpleGraph.{0} V) (Set.{0} (SimpleGraph.{0} V))
          (@Set.instInsert.{0} (SimpleGraph.{0} V)) u
          (@Set.Icc.{0} (SimpleGraph.{0} V)
            (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
            (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t))))
      (@sInf.{0} (OrderDual.{0} (SimpleGraph.{0} V))
        (@OrderInfSet.toInfSet.{0} (OrderDual.{0} (SimpleGraph.{0} V))
          (@Preorder.toLE.{0} (OrderDual.{0} (SimpleGraph.{0} V))
            (@OrderDual.instPreorder.{0} (SimpleGraph.{0} V)
              (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
                (@SimpleGraph.instPartialOrder.{0} V))))
          (@OrderDual.orderInfSet.{0} (SimpleGraph.{0} V)
            (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
            (@CompleteSemilatticeSup.toOrderSupSet.{0} (SimpleGraph.{0} V)
              (@CompleteLattice.toCompleteSemilatticeSup.{0} (SimpleGraph.{0} V)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                    (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V)))))))
        (@Set.preimage.{0, 0} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
            (OrderDual.{0} (SimpleGraph.{0} V)) (fun x ↦ SimpleGraph.{0} V)
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
              (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
              (@Equiv.instEquivLike.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)))
            (@OrderDual.ofDual.{0} (SimpleGraph.{0} V)))
          (@insert.{0, 0} (SimpleGraph.{0} V) (Set.{0} (SimpleGraph.{0} V))
            (@Set.instInsert.{0} (SimpleGraph.{0} V)) u
            (@Set.Icc.{0} (SimpleGraph.{0} V)
              (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
                (@SimpleGraph.instPartialOrder.{0} V))
              (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t)))))
      (@DFunLike.coe.{1, 1, 1}
        (Equiv.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V))) (SimpleGraph.{0} V)
        (fun x ↦ OrderDual.{0} (SimpleGraph.{0} V))
        (@EquivLike.toFunLike.{1, 1, 1}
          (Equiv.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V))) (SimpleGraph.{0} V)
          (OrderDual.{0} (SimpleGraph.{0} V))
          (@Equiv.instEquivLike.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V))))
        (@OrderDual.toDual.{0} (SimpleGraph.{0} V))
        (@max.{0} (SimpleGraph.{0} V)
          (@SemilatticeSup.toMax.{0} (SimpleGraph.{0} V)
            (@Lattice.toSemilatticeSup.{0} (SimpleGraph.{0} V)
              (@CompleteLattice.toLattice.{0} (SimpleGraph.{0} V)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                    (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V))))))
          u (@SimpleGraph.fromEdgeSet.{0} V t)))
      (@IsGLB.isGLB_sInf.{0} (OrderDual.{0} (SimpleGraph.{0} V))
        (@OrderDual.instPreorder.{0} (SimpleGraph.{0} V)
          (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V)))
        (@OrderDual.orderInfSet.{0} (SimpleGraph.{0} V)
          (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
          (@CompleteSemilatticeSup.toOrderSupSet.{0} (SimpleGraph.{0} V)
            (@CompleteLattice.toCompleteSemilatticeSup.{0} (SimpleGraph.{0} V)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                  (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V))))))
        (@Set.preimage.{0, 0} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
            (OrderDual.{0} (SimpleGraph.{0} V)) (fun x ↦ SimpleGraph.{0} V)
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V))
              (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)
              (@Equiv.instEquivLike.{1, 1} (OrderDual.{0} (SimpleGraph.{0} V)) (SimpleGraph.{0} V)))
            (@OrderDual.ofDual.{0} (SimpleGraph.{0} V)))
          (@insert.{0, 0} (SimpleGraph.{0} V) (Set.{0} (SimpleGraph.{0} V))
            (@Set.instInsert.{0} (SimpleGraph.{0} V)) u
            (@Set.Icc.{0} (SimpleGraph.{0} V)
              (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
                (@SimpleGraph.instPartialOrder.{0} V))
              (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t))))
        (@DFunLike.coe.{1, 1, 1}
          (Equiv.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V))) (SimpleGraph.{0} V)
          (fun x ↦ OrderDual.{0} (SimpleGraph.{0} V))
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V)))
            (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V))
            (@Equiv.instEquivLike.{1, 1} (SimpleGraph.{0} V) (OrderDual.{0} (SimpleGraph.{0} V))))
          (@OrderDual.toDual.{0} (SimpleGraph.{0} V))
          (@max.{0} (SimpleGraph.{0} V)
            (@SemilatticeSup.toMax.{0} (SimpleGraph.{0} V)
              (@Lattice.toSemilatticeSup.{0} (SimpleGraph.{0} V)
                (@CompleteLattice.toLattice.{0} (SimpleGraph.{0} V)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                      (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V))))))
            u (@SimpleGraph.fromEdgeSet.{0} V t)))
        (@IsLUB.dual.{0} (SimpleGraph.{0} V)
          (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
          (@insert.{0, 0} (SimpleGraph.{0} V) (Set.{0} (SimpleGraph.{0} V))
            (@Set.instInsert.{0} (SimpleGraph.{0} V)) u
            (@Set.Icc.{0} (SimpleGraph.{0} V)
              (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
                (@SimpleGraph.instPartialOrder.{0} V))
              (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t)))
          (@max.{0} (SimpleGraph.{0} V)
            (@SemilatticeSup.toMax.{0} (SimpleGraph.{0} V)
              (@Lattice.toSemilatticeSup.{0} (SimpleGraph.{0} V)
                (@CompleteLattice.toLattice.{0} (SimpleGraph.{0} V)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                      (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V))))))
            u (@SimpleGraph.fromEdgeSet.{0} V t))
          (@IsLUB.insert.{0} (SimpleGraph.{0} V)
            (@Lattice.toSemilatticeSup.{0} (SimpleGraph.{0} V)
              (@CompleteLattice.toLattice.{0} (SimpleGraph.{0} V)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                    (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V)))))
            u (@SimpleGraph.fromEdgeSet.{0} V t)
            (@Set.Icc.{0} (SimpleGraph.{0} V)
              (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
                (@SimpleGraph.instPartialOrder.{0} V))
              (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t))
            (@isLUB_Icc.{0} (SimpleGraph.{0} V)
              (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V)
                (@SimpleGraph.instPartialOrder.{0} V))
              (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t)
              (@SimpleGraph.fromEdgeSet_mono.{0} V s t h)))))
      (@IsLUB.dual.{0} (SimpleGraph.{0} V)
        (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
        (@insert.{0, 0} (SimpleGraph.{0} V) (Set.{0} (SimpleGraph.{0} V))
          (@Set.instInsert.{0} (SimpleGraph.{0} V)) u
          (@Set.Icc.{0} (SimpleGraph.{0} V)
            (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
            (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t)))
        (@max.{0} (SimpleGraph.{0} V)
          (@SemilatticeSup.toMax.{0} (SimpleGraph.{0} V)
            (@Lattice.toSemilatticeSup.{0} (SimpleGraph.{0} V)
              (@CompleteLattice.toLattice.{0} (SimpleGraph.{0} V)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                    (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V))))))
          u (@SimpleGraph.fromEdgeSet.{0} V t))
        (@IsLUB.insert.{0} (SimpleGraph.{0} V)
          (@Lattice.toSemilatticeSup.{0} (SimpleGraph.{0} V)
            (@CompleteLattice.toLattice.{0} (SimpleGraph.{0} V)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (SimpleGraph.{0} V)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (SimpleGraph.{0} V)
                  (@SimpleGraph.completeAtomicBooleanAlgebra.{0} V)))))
          u (@SimpleGraph.fromEdgeSet.{0} V t)
          (@Set.Icc.{0} (SimpleGraph.{0} V)
            (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
            (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t))
          (@isLUB_Icc.{0} (SimpleGraph.{0} V)
            (@PartialOrder.toPreorder.{0} (SimpleGraph.{0} V) (@SimpleGraph.instPartialOrder.{0} V))
            (@SimpleGraph.fromEdgeSet.{0} V s) (@SimpleGraph.fromEdgeSet.{0} V t)
            (@SimpleGraph.fromEdgeSet_mono.{0} V s t h))))
  -- Phase 1: Redundant implication-chain mediation
  have h_med_1 : ∀ {P : Prop}, P → (True → P) ∧ (P → P) := fun hp =>
    And.intro (fun _ => id hp) (fun h => (And.intro h hp).1)
  have h_stage_1 := (h_med_1 h_core).2 ((h_med_1 h_core).1 True.intro)
  -- Phase 2: Inductive case-analysis ceremony on a trivial index
  have h_lift_2 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_2 := h_lift_2 h_stage_1 0 rfl
  -- Phase 3: Redundant implication-chain mediation
  have h_med_3 : ∀ {P : Prop}, P → (True → P) ∧ (P → P) := fun hp =>
    And.intro (fun _ => id hp) (fun h => (And.intro h hp).1)
  have h_stage_3 := (h_med_3 h_stage_2).2 ((h_med_3 h_stage_2).1 True.intro)
  -- Final step: conclude after 3 auxiliary verification stage(s)
  exact id h_stage_3
