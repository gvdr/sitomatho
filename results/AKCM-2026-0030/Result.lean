import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Subrepresentation.coe_sup (Subrepresentation)
-- Step 1: ssubset_of_eq_of_ssubset (ssubset_of_eq_of_ssubset)
-- Step 6: Set.Iio_ssubset_Iio (Set)
-- Step 7: ne_top_of_lt (ne_top_of_lt)
-- Step 8: Set.encard_pair (Set)
-- Step 9: Eq.rightDvd (Eq)
theorem akcm_2026_0030
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
  u) :
    @RightDvd.{0} ENat
  (@Monoid.toSemigroup.{0} ENat
    (@Semiring.toMonoid.{0} ENat
      (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)))
  (@Set.encard.{0} (Set.{0} (Set.{0} W))
    (@insert.{0, 0} (Set.{0} (Set.{0} W)) (Set.{0} (Set.{0} (Set.{0} W)))
      (@Set.instInsert.{0} (Set.{0} (Set.{0} W)))
      (@Set.Iio.{0} (Set.{0} W)
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
            (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
            x_9 x_10)))
      (@singleton.{0, 0} (Set.{0} (Set.{0} W)) (Set.{0} (Set.{0} (Set.{0} W)))
        (@Set.instSingletonSet.{0} (Set.{0} (Set.{0} W)))
        (@Top.top.{0} (Set.{0} (Set.{0} W))
          (@OrderTop.toTop.{0} (Set.{0} (Set.{0} W))
            (@Preorder.toLE.{0} (Set.{0} (Set.{0} W))
              (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} W))
                (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} (Set.{0} W))
                  (@ChainCompletePartialOrder.instOfCompleteLattice.{0}
                    (Set.{0} (Set.{0} W))
                    (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} W))
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                        (Set.{0} (Set.{0} W))
                        (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} W))))))))
            (@Set.instOrderTop.{0} (Set.{0} W)))))))
  (@OfNat.ofNat.{0} ENat (nat_lit 2)
    (@instOfNatAtLeastTwo.{0} ENat (nat_lit 2) ENat.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Nat.instNeZeroSucc
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) :=   @Eq.rightDvd.{0} ENat
  (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
  (@Set.encard.{0} (Set.{0} (Set.{0} W))
    (@insert.{0, 0} (Set.{0} (Set.{0} W)) (Set.{0} (Set.{0} (Set.{0} W)))
      (@Set.instInsert.{0} (Set.{0} (Set.{0} W)))
      (@Set.Iio.{0} (Set.{0} W)
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
            x_10)))
      (@singleton.{0, 0} (Set.{0} (Set.{0} W)) (Set.{0} (Set.{0} (Set.{0} W)))
        (@Set.instSingletonSet.{0} (Set.{0} (Set.{0} W)))
        (@Top.top.{0} (Set.{0} (Set.{0} W))
          (@OrderTop.toTop.{0} (Set.{0} (Set.{0} W))
            (@Preorder.toLE.{0} (Set.{0} (Set.{0} W))
              (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} W))
                (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} (Set.{0} W))
                  (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} (Set.{0} W))
                    (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} W))
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                        (Set.{0} (Set.{0} W))
                        (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} W))))))))
            (@Set.instOrderTop.{0} (Set.{0} W)))))))
  (@OfNat.ofNat.{0} ENat (nat_lit 2)
    (@instOfNatAtLeastTwo.{0} ENat (nat_lit 2) ENat.instNatCast
      (@Nat.instAtLeastTwoHAddOfNat
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
  (@Set.encard_pair.{0} (Set.{0} (Set.{0} W))
    (@Set.Iio.{0} (Set.{0} W)
      (@PartialOrder.toPreorder.{0} (Set.{0} W)
        (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
      (@SetLike.coe.{0, 0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) W
        (@Subrepresentation.instSetLike.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
        (@max.{0} (@Subrepresentation.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ)
          (@Subrepresentation.instMax.{0, 0, 0} A G W inst_4 inst_5 inst_6 inst_7 ρ) x_9 x_10)))
    (@Top.top.{0} (Set.{0} (Set.{0} W))
      (@OrderTop.toTop.{0} (Set.{0} (Set.{0} W))
        (@Preorder.toLE.{0} (Set.{0} (Set.{0} W))
          (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} W))
            (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} (Set.{0} W))
              (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} (Set.{0} W))
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} W))
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                    (Set.{0} (Set.{0} W))
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} W))))))))
        (@Set.instOrderTop.{0} (Set.{0} W))))
    (@ne_top_of_lt.{0} (Set.{0} (Set.{0} W))
      (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} W))
        (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} (Set.{0} W))
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} (Set.{0} W))
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} W))
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Set.{0} W))
                (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} W)))))))
      (@Set.instOrderTop.{0} (Set.{0} W))
      (@Set.Iio.{0} (Set.{0} W)
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
            x_10)))
      (@Set.Iio.{0} (Set.{0} W)
        (@PartialOrder.toPreorder.{0} (Set.{0} W)
          (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} W)
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} W)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} W)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} W)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} W))))))
        u)
      (@Set.Iio_ssubset_Iio.{0} (Set.{0} W)
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
        u
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
          h_12))))
