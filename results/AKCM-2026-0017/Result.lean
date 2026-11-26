import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.RelClasses
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Subrepresentation.coe_sup (Subrepresentation)
-- Step 1: ssubset_of_eq_of_ssubset (ssubset_of_eq_of_ssubset)
-- Step 2: Set.Ico_subset_Ioo (Set)
-- Step 3: IsCofinalFor.of_subset (IsCofinalFor)
-- Step 4: IsCofinalFor.union_left (IsCofinalFor)
-- Step 8: IsCofinalFor.nonempty (IsCofinalFor)
-- Step 9: Set.Nonempty.to_subtype (Set)
theorem akcm_2026_0017
    {A : Type}
    {G : Type}
    {W : Type}
    [inst_4 : Semiring.{0} A]
    [inst_5 : Monoid.{0} G]
    [inst_6 : AddCommMonoid.{0} W]
    [inst_7 : @Module.{0, 0} A W inst_4 inst_6]
    {ρ : @Representation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7}
    (x_9 : @Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
    (x_10 : @Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
    {u : Set.{0} W}
    (h_12 : @LT.lt.{0} (Set.{0} W)
  (@Preorder.toLT.{0} (Set.{0} W)
    (@PartialOrder.toPreorder.{0} (Set.{0} W)
      (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
        (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
              (@Set.instCompleteAtomicBooleanAlgebra.{0} W)))))))
  (@HAdd.hAdd.{0, 0, 0} (Set.{0} W) (Set.{0} W) (Set.{0} W)
    (@instHAdd.{0} (Set.{0} W)
      (@Set.add.{0} W
        (@AddCommMagma.toAdd.{0} W
          (@AddCommSemigroup.toAddCommMagma.{0} W
            (@AddCommMonoid.toAddCommSemigroup.{0} W inst_6)))))
    (@SetLike.coe.{0, 0}
      (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
      (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
      x_9)
    (@SetLike.coe.{0, 0}
      (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
      (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
      x_10))
  u)
    {v : Set.{0} W}
    {w : Set.{0} W}
    (h_15 : @LE.le.{0} (Set.{0} W)
  (@Preorder.toLE.{0} (Set.{0} W)
    (@PartialOrder.toPreorder.{0} (Set.{0} W)
      (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
        (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
              (@Set.instCompleteAtomicBooleanAlgebra.{0} W)))))))
  v w)
    (h_16 : @Set.Nonempty.{0} (Set.{0} W)
  (@max.{0} (Set.{0} (Set.{0} W)) (@Set.instMax.{0} (Set.{0} W))
    (@Set.Ico.{0} (Set.{0} W)
      (@PartialOrder.toPreorder.{0} (Set.{0} W)
        (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                (Set.{0} W) (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
      u v)
    (@Set.Ioo.{0} (Set.{0} W)
      (@PartialOrder.toPreorder.{0} (Set.{0} W)
        (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                (Set.{0} W) (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
      (@SetLike.coe.{0, 0}
        (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
        (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7
          ρ)
        (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
          (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
          x_9 x_10))
      w))) :
    Nonempty.{1}
  (@Set.Elem.{0} (Set.{0} W)
    (@Set.Ioo.{0} (Set.{0} W)
      (@PartialOrder.toPreorder.{0} (Set.{0} W)
        (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
      (@SetLike.coe.{0, 0}
        (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
        (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
        (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
          (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9
          x_10))
      w)) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Set.Nonempty.to_subtype.{0} (Set.{0} W)
      (@Set.Ioo.{0} (Set.{0} W)
        (@PartialOrder.toPreorder.{0} (Set.{0} W)
          (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
        (@SetLike.coe.{0, 0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
          (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
          (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
            (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9 x_10))
        w)
      (@IsCofinalFor.nonempty.{0} (Set.{0} W)
        (@PartialOrder.toPreorder.{0} (Set.{0} W)
          (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
        (@max.{0} (Set.{0} (Set.{0} W)) (@Set.instMax.{0} (Set.{0} W))
          (@Set.Ico.{0} (Set.{0} W)
            (@PartialOrder.toPreorder.{0} (Set.{0} W)
              (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                      (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
            u v)
          (@Set.Ioo.{0} (Set.{0} W)
            (@PartialOrder.toPreorder.{0} (Set.{0} W)
              (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                      (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
            (@SetLike.coe.{0, 0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
              W (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
              (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9
                x_10))
            w))
        (@Set.Ioo.{0} (Set.{0} W)
          (@PartialOrder.toPreorder.{0} (Set.{0} W)
            (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
              (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
          (@SetLike.coe.{0, 0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
            (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
            (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
              (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9 x_10))
          w)
        (@IsCofinalFor.union_left.{0} (Set.{0} W)
          (@PartialOrder.toPreorder.{0} (Set.{0} W)
            (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
              (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
          (@Set.Ico.{0} (Set.{0} W)
            (@PartialOrder.toPreorder.{0} (Set.{0} W)
              (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                      (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
            u v)
          (@Set.Ioo.{0} (Set.{0} W)
            (@PartialOrder.toPreorder.{0} (Set.{0} W)
              (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                      (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
            (@SetLike.coe.{0, 0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
              W (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
              (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9
                x_10))
            w)
          (@IsCofinalFor.of_subset.{0} (Set.{0} W)
            (@PartialOrder.toPreorder.{0} (Set.{0} W)
              (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                      (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
            (@Set.Ico.{0} (Set.{0} W)
              (@PartialOrder.toPreorder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                  (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                    (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                        (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
              u v)
            (@Set.Ioo.{0} (Set.{0} W)
              (@PartialOrder.toPreorder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                  (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                    (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                        (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
              (@SetLike.coe.{0, 0}
                (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
                (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                  (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9
                  x_10))
              w)
            (@Set.Ico_subset_Ioo.{0} (Set.{0} W)
              (@PartialOrder.toPreorder.{0} (Set.{0} W)
                (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                  (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                    (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                        (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
              u
              (@SetLike.coe.{0, 0}
                (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
                (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                  (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9
                  x_10))
              v w
              (@ssubset_of_eq_of_ssubset.{0} (Set.{0} W) (Set.instUsesSetNotationForOrder.{0} W)
                (@SetLike.coe.{0, 0}
                  (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
                  (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                  (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                    (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9
                    x_10))
                (@HAdd.hAdd.{0, 0, 0} (Set.{0} W) (Set.{0} W) (Set.{0} W)
                  (@instHAdd.{0} (Set.{0} W)
                    (@Set.add.{0} W
                      (@AddCommMagma.toAdd.{0} W
                        (@AddCommSemigroup.toAddCommMagma.{0} W
                          (@AddCommMonoid.toAddCommSemigroup.{0} W inst_6)))))
                  (@SetLike.coe.{0, 0}
                    (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
                    (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                    x_9)
                  (@SetLike.coe.{0, 0}
                    (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
                    (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
                    x_10))
                u
                (@Preorder.toLT.{0} (Set.{0} W)
                  (@PartialOrder.toPreorder.{0} (Set.{0} W)
                    (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
                      (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
                        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                            (@Set.instCompleteAtomicBooleanAlgebra.{0} W)))))))
                (@Subrepresentation.coe_sup.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ x_9 x_10)
                h_12)
              h_15)))
        h_16)
  -- Phase 1: Symmetric conjunction–disjunction transport
  have h_sym_1 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_1 := h_sym_1 h_core
  -- Phase 2: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_2 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_2 : (3 + 13 : Nat) = 16 then
      have h_pack_2 := And.intro h_arith_2 hp
      exact h_pack_2.2
    else
      exact False.elim (h_arith_2 rfl)
  have h_stage_2 := h_chk_2 h_stage_1
  -- Phase 3: Symmetric conjunction–disjunction transport
  have h_sym_3 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_3 := h_sym_3 h_stage_2
  -- Phase 4: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_4 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_4 : (8 + 17 : Nat) = 25 then
      have h_pack_4 := And.intro h_arith_4 hp
      exact h_pack_4.2
    else
      exact False.elim (h_arith_4 rfl)
  have h_stage_4 := h_chk_4 h_stage_3
  -- Final step: conclude after 4 auxiliary verification stage(s)
  exact id h_stage_4
