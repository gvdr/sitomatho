import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Cover
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.OrderDual
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: OrdinalApprox.gfpApprox_le (OrdinalApprox)
-- Step 1: isLeast_Icc (isLeast_Icc)
-- Step 3: IsLeast.csInf_mem (IsLeast)
-- Step 5: Set.sdiff_singleton_covBy (Set)
-- Step 8: CovBy.toDual (CovBy)
-- Step 9: CovBy.Ioo_eq (CovBy)
theorem akcm_2026_0010
    {α : Type}
    [inst_2 : CompleteLattice.{0} α]
    (f : @OrderHom.{0, 0} α α
  (@PartialOrder.toPreorder.{0} α
    (@ChainCompletePartialOrder.toPartialOrder.{0} α
      (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
  (@PartialOrder.toPreorder.{0} α
    (@ChainCompletePartialOrder.toPartialOrder.{0} α
      (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2))))
    {x : α}
    {a : Ordinal.{0}} :
    @Eq.{1} (Set.{0} (OrderDual.{0} (Set.{0} α)))
  (@Set.Ioo.{0} (OrderDual.{0} (Set.{0} α))
    (@OrderDual.instPreorder.{0} (Set.{0} α)
      (@PartialOrder.toPreorder.{0} (Set.{0} α)
        (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} α)
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} α)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                (@Set.instCompleteAtomicBooleanAlgebra.{0} α)))))))
    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α)))
      (Set.{0} α) (fun x ↦ OrderDual.{0} (Set.{0} α))
      (@EquivLike.toFunLike.{1, 1, 1}
        (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))) (Set.{0} α)
        (OrderDual.{0} (Set.{0} α))
        (@Equiv.instEquivLike.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))))
      (@OrderDual.toDual.{0} (Set.{0} α))
      (@Set.Icc.{0} α
        (@PartialOrder.toPreorder.{0} α
          (@ChainCompletePartialOrder.toPartialOrder.{0} α
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
        (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x))
    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α)))
      (Set.{0} α) (fun x ↦ OrderDual.{0} (Set.{0} α))
      (@EquivLike.toFunLike.{1, 1, 1}
        (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))) (Set.{0} α)
        (OrderDual.{0} (Set.{0} α))
        (@Equiv.instEquivLike.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))))
      (@OrderDual.toDual.{0} (Set.{0} α))
      (@sdiff.{0} (Set.{0} α) (@Set.instSDiff.{0} α)
        (@Set.Icc.{0} α
          (@PartialOrder.toPreorder.{0} α
            (@ChainCompletePartialOrder.toPartialOrder.{0} α
              (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
          (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x)
        (@singleton.{0, 0} α (Set.{0} α) (@Set.instSingletonSet.{0} α)
          (@sInf.{0} α
            (@ConditionallyCompletePartialOrderInf.toInfSet.{0} α
              (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderInf.{0}
                α
                (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} α
                  (@CompleteLattice.toConditionallyCompleteLattice.{0} α inst_2))))
            (@Set.Icc.{0} α
              (@PartialOrder.toPreorder.{0} α
                (@ChainCompletePartialOrder.toPartialOrder.{0} α
                  (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
              (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x))))))
  (@EmptyCollection.emptyCollection.{0} (Set.{0} (OrderDual.{0} (Set.{0} α)))
    (@Set.instEmptyCollection.{0} (OrderDual.{0} (Set.{0} α)))) :=   @CovBy.Ioo_eq.{0} (OrderDual.{0} (Set.{0} α))
  (@OrderDual.instPreorder.{0} (Set.{0} α)
    (@PartialOrder.toPreorder.{0} (Set.{0} α)
      (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} α)
        (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} α)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
              (@Set.instCompleteAtomicBooleanAlgebra.{0} α)))))))
  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))) (Set.{0} α)
    (fun x ↦ OrderDual.{0} (Set.{0} α))
    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α)))
      (Set.{0} α) (OrderDual.{0} (Set.{0} α))
      (@Equiv.instEquivLike.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))))
    (@OrderDual.toDual.{0} (Set.{0} α))
    (@Set.Icc.{0} α
      (@PartialOrder.toPreorder.{0} α
        (@ChainCompletePartialOrder.toPartialOrder.{0} α
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
      (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x))
  (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))) (Set.{0} α)
    (fun x ↦ OrderDual.{0} (Set.{0} α))
    (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α)))
      (Set.{0} α) (OrderDual.{0} (Set.{0} α))
      (@Equiv.instEquivLike.{1, 1} (Set.{0} α) (OrderDual.{0} (Set.{0} α))))
    (@OrderDual.toDual.{0} (Set.{0} α))
    (@sdiff.{0} (Set.{0} α) (@Set.instSDiff.{0} α)
      (@Set.Icc.{0} α
        (@PartialOrder.toPreorder.{0} α
          (@ChainCompletePartialOrder.toPartialOrder.{0} α
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
        (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x)
      (@singleton.{0, 0} α (Set.{0} α) (@Set.instSingletonSet.{0} α)
        (@sInf.{0} α
          (@ConditionallyCompletePartialOrderInf.toInfSet.{0} α
            (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderInf.{0} α
              (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} α
                (@CompleteLattice.toConditionallyCompleteLattice.{0} α inst_2))))
          (@Set.Icc.{0} α
            (@PartialOrder.toPreorder.{0} α
              (@ChainCompletePartialOrder.toPartialOrder.{0} α
                (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
            (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x)))))
  (@CovBy.toDual.{0} (Set.{0} α)
    (@Preorder.toLT.{0} (Set.{0} α)
      (@PartialOrder.toPreorder.{0} (Set.{0} α)
        (@SemilatticeInf.toPartialOrder.{0} (Set.{0} α)
          (@Lattice.toSemilatticeInf.{0} (Set.{0} α)
            (@GeneralizedCoheytingAlgebra.toLattice.{0} (Set.{0} α)
              (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} (Set.{0} α)
                (@BiheytingAlgebra.toCoheytingAlgebra.{0} (Set.{0} α)
                  (@BooleanAlgebra.toBiheytingAlgebra.{0} (Set.{0} α)
                    (@Set.instBooleanAlgebra.{0} α)))))))))
    (@sdiff.{0} (Set.{0} α) (@Set.instSDiff.{0} α)
      (@Set.Icc.{0} α
        (@PartialOrder.toPreorder.{0} α
          (@ChainCompletePartialOrder.toPartialOrder.{0} α
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
        (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x)
      (@singleton.{0, 0} α (Set.{0} α) (@Set.instSingletonSet.{0} α)
        (@sInf.{0} α
          (@ConditionallyCompletePartialOrderInf.toInfSet.{0} α
            (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderInf.{0} α
              (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} α
                (@CompleteLattice.toConditionallyCompleteLattice.{0} α inst_2))))
          (@Set.Icc.{0} α
            (@PartialOrder.toPreorder.{0} α
              (@ChainCompletePartialOrder.toPartialOrder.{0} α
                (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
            (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x))))
    (@Set.Icc.{0} α
      (@PartialOrder.toPreorder.{0} α
        (@ChainCompletePartialOrder.toPartialOrder.{0} α
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
      (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x)
    (@Set.sdiff_singleton_covBy.{0} α
      (@Set.Icc.{0} α
        (@PartialOrder.toPreorder.{0} α
          (@ChainCompletePartialOrder.toPartialOrder.{0} α
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
        (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x)
      (@sInf.{0} α
        (@ConditionallyCompletePartialOrderInf.toInfSet.{0} α
          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderInf.{0} α
            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} α
              (@CompleteLattice.toConditionallyCompleteLattice.{0} α inst_2))))
        (@Set.Icc.{0} α
          (@PartialOrder.toPreorder.{0} α
            (@ChainCompletePartialOrder.toPartialOrder.{0} α
              (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
          (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x))
      (@IsLeast.csInf_mem.{0} α
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderInf.{0} α
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} α
            (@CompleteLattice.toConditionallyCompleteLattice.{0} α inst_2)))
        (@Set.Icc.{0} α
          (@PartialOrder.toPreorder.{0} α
            (@ChainCompletePartialOrder.toPartialOrder.{0} α
              (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
          (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a) x)
        (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a)
        (@isLeast_Icc.{0} α
          (@PartialOrder.toPreorder.{0} α
            (@ChainCompletePartialOrder.toPartialOrder.{0} α
              (@ChainCompletePartialOrder.instOfCompleteLattice.{0} α inst_2)))
          x (@OrdinalApprox.gfpApprox.{0} α inst_2 f x a)
          (@OrdinalApprox.gfpApprox_le.{0} α inst_2 f x a)))))
