import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Order.UpperLower.CompleteLattice

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: UpperSet.coe_sInf (UpperSet)
-- Step 1: subset_of_eq_of_subset (subset_of_eq_of_subset)
-- Step 2: sdiff_sdiff_sdiff_cancel_right (sdiff_sdiff_sdiff_cancel_right)
-- Step 3: subset_of_eq (subset_of_eq)
-- Step 4: Set.ssubset_of_subset_of_ssubset (Set)
-- Step 5: isGreatest_Ioc (isGreatest_Ioc)
-- Step 6: IsGreatest.nonempty (IsGreatest)
-- Step 7: Set.Nonempty.empty_ssubset (Set)
-- Step 8: LT.lt.not_superset (LT)
-- Step 9: ne_of_not_subset (ne_of_not_subset)
theorem akcm_2026_0013
    {α : Type}
    [inst_2 : LE.{0} α]
    (S : Set.{0} (@UpperSet.{0} α inst_2))
    {u : Set.{0} α}
    (h_5 : @LE.le.{0} (Set.{0} α) (@Set.instLE.{0} α)
  (⋃ s,
    ⋃ (_ :
      @Membership.mem.{0, 0} (@UpperSet.{0} α inst_2)
        (Set.{0} (@UpperSet.{0} α inst_2))
        (@Set.instMembership.{0} (@UpperSet.{0} α inst_2)) S s),
      @SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
        (@UpperSet.instSetLike.{0} α inst_2) s)
  u)
    {v : Set.{0} α}
    {w : Set.{0} α}
    (h_8 : @LT.lt.{0} (Set.{0} α)
  (@Preorder.toLT.{0} (Set.{0} α)
    (@PartialOrder.toPreorder.{0} (Set.{0} α)
      (@SemilatticeInf.toPartialOrder.{0} (Set.{0} α)
        (@Lattice.toSemilatticeInf.{0} (Set.{0} α)
          (@DistribLattice.toLattice.{0} (Set.{0} α)
            (@Set.instDistribLattice.{0} α))))))
  (@sdiff.{0} (Set.{0} α)
    (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
      (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
        (@Set.instBooleanAlgebra.{0} α)))
    v u)
  w) :
    @Ne.{1} (Set.{0} (Set.{0} α))
  (@Set.Ioc.{0} (Set.{0} α)
    (@PartialOrder.toPreorder.{0} (Set.{0} α)
      (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
        (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
              (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
    (@sdiff.{0} (Set.{0} α)
      (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
        (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
          (@Set.instBooleanAlgebra.{0} α)))
      (@sdiff.{0} (Set.{0} α)
        (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
          (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
            (@Set.instBooleanAlgebra.{0} α)))
        v
        (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
          (@UpperSet.instSetLike.{0} α inst_2)
          (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
      (@sdiff.{0} (Set.{0} α)
        (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
          (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
            (@Set.instBooleanAlgebra.{0} α)))
        u
        (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
          (@UpperSet.instSetLike.{0} α inst_2)
          (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))))
    w)
  (@EmptyCollection.emptyCollection.{0} (Set.{0} (Set.{0} α))
    (@Set.instEmptyCollection.{0} (Set.{0} α))) :=   @ne_of_not_subset.{0} (Set.{0} (Set.{0} α)) (Set.instUsesSetNotationForOrder.{0} (Set.{0} α))
  (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} α))
    (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} (Set.{0} α))
      (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} (Set.{0} α))
        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} α))
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Set.{0} α))
            (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} α)))))))
  (@Set.Ioc.{0} (Set.{0} α)
    (@PartialOrder.toPreorder.{0} (Set.{0} α)
      (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
        (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
              (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
    (@sdiff.{0} (Set.{0} α)
      (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
        (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
          (@Set.instBooleanAlgebra.{0} α)))
      (@sdiff.{0} (Set.{0} α)
        (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
          (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
            (@Set.instBooleanAlgebra.{0} α)))
        v
        (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α (@UpperSet.instSetLike.{0} α inst_2)
          (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
      (@sdiff.{0} (Set.{0} α)
        (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
          (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
            (@Set.instBooleanAlgebra.{0} α)))
        u
        (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α (@UpperSet.instSetLike.{0} α inst_2)
          (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))))
    w)
  (@EmptyCollection.emptyCollection.{0} (Set.{0} (Set.{0} α))
    (@Set.instEmptyCollection.{0} (Set.{0} α)))
  (@LT.lt.not_superset.{0} (Set.{0} (Set.{0} α))
    (Set.instUsesSetNotationForOrder.{0} (Set.{0} α))
    (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} α))
      (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} (Set.{0} α))
        (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} (Set.{0} α))
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} α))
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Set.{0} α))
              (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} α)))))))
    (@EmptyCollection.emptyCollection.{0} (Set.{0} (Set.{0} α))
      (@Set.instEmptyCollection.{0} (Set.{0} α)))
    (@Set.Ioc.{0} (Set.{0} α)
      (@PartialOrder.toPreorder.{0} (Set.{0} α)
        (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
          (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
      (@sdiff.{0} (Set.{0} α)
        (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
          (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
            (@Set.instBooleanAlgebra.{0} α)))
        (@sdiff.{0} (Set.{0} α)
          (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
            (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
              (@Set.instBooleanAlgebra.{0} α)))
          v
          (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α (@UpperSet.instSetLike.{0} α inst_2)
            (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
        (@sdiff.{0} (Set.{0} α)
          (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
            (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
              (@Set.instBooleanAlgebra.{0} α)))
          u
          (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α (@UpperSet.instSetLike.{0} α inst_2)
            (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))))
      w)
    (@Set.Nonempty.empty_ssubset.{0} (Set.{0} α)
      (@Set.Ioc.{0} (Set.{0} α)
        (@PartialOrder.toPreorder.{0} (Set.{0} α)
          (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
            (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
        (@sdiff.{0} (Set.{0} α)
          (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
            (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
              (@Set.instBooleanAlgebra.{0} α)))
          (@sdiff.{0} (Set.{0} α)
            (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
              (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                (@Set.instBooleanAlgebra.{0} α)))
            v
            (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α (@UpperSet.instSetLike.{0} α inst_2)
              (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
          (@sdiff.{0} (Set.{0} α)
            (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
              (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                (@Set.instBooleanAlgebra.{0} α)))
            u
            (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α (@UpperSet.instSetLike.{0} α inst_2)
              (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))))
        w)
      (@IsGreatest.nonempty.{0} (Set.{0} α)
        (@PartialOrder.toPreorder.{0} (Set.{0} α)
          (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
            (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
        (@Set.Ioc.{0} (Set.{0} α)
          (@PartialOrder.toPreorder.{0} (Set.{0} α)
            (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
              (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
          (@sdiff.{0} (Set.{0} α)
            (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
              (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                (@Set.instBooleanAlgebra.{0} α)))
            (@sdiff.{0} (Set.{0} α)
              (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instBooleanAlgebra.{0} α)))
              v
              (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                (@UpperSet.instSetLike.{0} α inst_2)
                (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
            (@sdiff.{0} (Set.{0} α)
              (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instBooleanAlgebra.{0} α)))
              u
              (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                (@UpperSet.instSetLike.{0} α inst_2)
                (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))))
          w)
        w
        (@isGreatest_Ioc.{0} (Set.{0} α)
          (@PartialOrder.toPreorder.{0} (Set.{0} α)
            (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
              (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
          (@sdiff.{0} (Set.{0} α)
            (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
              (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                (@Set.instBooleanAlgebra.{0} α)))
            (@sdiff.{0} (Set.{0} α)
              (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instBooleanAlgebra.{0} α)))
              v
              (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                (@UpperSet.instSetLike.{0} α inst_2)
                (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
            (@sdiff.{0} (Set.{0} α)
              (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instBooleanAlgebra.{0} α)))
              u
              (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                (@UpperSet.instSetLike.{0} α inst_2)
                (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))))
          w
          (@Set.ssubset_of_subset_of_ssubset.{0} α
            (@sdiff.{0} (Set.{0} α)
              (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instBooleanAlgebra.{0} α)))
              (@sdiff.{0} (Set.{0} α)
                (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                  (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                    (@Set.instBooleanAlgebra.{0} α)))
                v
                (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                  (@UpperSet.instSetLike.{0} α inst_2)
                  (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
              (@sdiff.{0} (Set.{0} α)
                (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                  (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                    (@Set.instBooleanAlgebra.{0} α)))
                u
                (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                  (@UpperSet.instSetLike.{0} α inst_2)
                  (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))))
            (@sdiff.{0} (Set.{0} α)
              (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instBooleanAlgebra.{0} α)))
              v u)
            w
            (@subset_of_eq.{0} (Set.{0} α) (Set.instUsesSetNotationForOrder.{0} α)
              (@PartialOrder.toPreorder.{0} (Set.{0} α)
                (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
                  (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
                    (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                        (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
              (@sdiff.{0} (Set.{0} α)
                (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                  (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                    (@Set.instBooleanAlgebra.{0} α)))
                (@sdiff.{0} (Set.{0} α)
                  (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                    (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                      (@Set.instBooleanAlgebra.{0} α)))
                  v
                  (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                    (@UpperSet.instSetLike.{0} α inst_2)
                    (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S)))
                (@sdiff.{0} (Set.{0} α)
                  (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                    (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                      (@Set.instBooleanAlgebra.{0} α)))
                  u
                  (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                    (@UpperSet.instSetLike.{0} α inst_2)
                    (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2)
                      S))))
              (@sdiff.{0} (Set.{0} α)
                (@GeneralizedBooleanAlgebra.toSDiff.{0} (Set.{0} α)
                  (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                    (@Set.instBooleanAlgebra.{0} α)))
                v u)
              (@sdiff_sdiff_sdiff_cancel_right.{0} (Set.{0} α) v u
                (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                  (@UpperSet.instSetLike.{0} α inst_2)
                  (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))
                (@BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instBooleanAlgebra.{0} α))
                (@subset_of_eq_of_subset.{0} (Set.{0} α) (Set.instUsesSetNotationForOrder.{0} α)
                  (@SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                    (@UpperSet.instSetLike.{0} α inst_2)
                    (@sInf.{0} (@UpperSet.{0} α inst_2) (@UpperSet.instInfSet.{0} α inst_2) S))
                  (⋃ s,
                    ⋃ (_ :
                      @Membership.mem.{0, 0} (@UpperSet.{0} α inst_2)
                        (Set.{0} (@UpperSet.{0} α inst_2))
                        (@Set.instMembership.{0} (@UpperSet.{0} α inst_2)) S s),
                      @SetLike.coe.{0, 0} (@UpperSet.{0} α inst_2) α
                        (@UpperSet.instSetLike.{0} α inst_2) s)
                  u (@Set.instLE.{0} α) (@UpperSet.coe_sInf.{0} α inst_2 S) h_5)))
            h_8)))))
