import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.Basic.Opposite
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.RelClasses

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: SSet.Subcomplex.image_preimage_le (SSet)
-- Step 1: lowerBounds_Icc (lowerBounds_Icc)
-- Step 2: ssubset_of_ssubset_of_eq (ssubset_of_ssubset_of_eq)
-- Step 3: Set.Icc_subset_Ico_right (Set)
-- Step 4: LE.le.isCofinalFor (LE)
-- Step 6: IsLUB.of_isCofinalFor (IsLUB)
theorem akcm_2026_0013
    {X : SSet.{0}}
    {Y : SSet.{0}}
    (B : X.Subcomplex)
    (f : @Quiver.Hom.{0, 1} SSet.{0}
  (@CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0}
    (@CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0}
      (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        Type CategoryTheory.types.{0})))
  Y X)
    {u : Set.{0} X.Subcomplex}
    (h_6 : @LT.lt.{0} (Set.{0} X.Subcomplex)
  (@Preorder.toLT.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
        (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex)))))))))
  u
  (@lowerBounds.{0} X.Subcomplex
    (@Preorder.toLE.{0} X.Subcomplex
      (@PartialOrder.toPreorder.{0} X.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
          (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          X)))
    (@Set.Icc.{0} X.Subcomplex
      (@PartialOrder.toPreorder.{0} X.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
          (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          X))
      (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f) B)))
    {v : Set.{0} X.Subcomplex}
    {w : Set.{0} X.Subcomplex}
    (h_9 : @IsLUB.{0} (Set.{0} X.Subcomplex)
  (@Preorder.toLE.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
        (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex)))))))))
  (@Set.Icc.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
        (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
    v u)
  w)
    (h_10 : @LE.le.{0} (Set.{0} (Set.{0} X.Subcomplex)) (@Set.instLE.{0} (Set.{0} X.Subcomplex))
  (@Set.Ico.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
        (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
    v
    (@Set.Iic.{0} X.Subcomplex
      (@PartialOrder.toPreorder.{0} X.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
          (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          X))
      (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f)))
  (@Set.Icc.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
        (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
    v u)) :
    @IsLUB.{0} (Set.{0} X.Subcomplex)
  (@Preorder.toLE.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex)))))))))
  (@Set.Ico.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
    v
    (@Set.Iic.{0} X.Subcomplex
      (@PartialOrder.toPreorder.{0} X.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
          (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          X))
      (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f)))
  w :=   @IsLUB.of_isCofinalFor.{0} (Set.{0} X.Subcomplex)
  (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
    (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
        (Set.{0} X.Subcomplex)
        (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
          (Set.{0} X.Subcomplex)
          (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} X.Subcomplex)
                (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
  w
  (@Set.Icc.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
    v u)
  (@Set.Ico.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
    v
    (@Set.Iic.{0} X.Subcomplex
      (@PartialOrder.toPreorder.{0} X.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          X))
      (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f)))
  h_9 h_10
  (@LE.le.isCofinalFor.{0} (Set.{0} X.Subcomplex)
    (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
      (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
          (Set.{0} X.Subcomplex)
          (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
            (Set.{0} X.Subcomplex)
            (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} X.Subcomplex)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
    (@Set.Icc.{0} (Set.{0} X.Subcomplex)
      (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
            (Set.{0} X.Subcomplex)
            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                    (Set.{0} X.Subcomplex)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
      v u)
    (@Set.Ico.{0} (Set.{0} X.Subcomplex)
      (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
            (Set.{0} X.Subcomplex)
            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                    (Set.{0} X.Subcomplex)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
      v
      (@Set.Iic.{0} X.Subcomplex
        (@PartialOrder.toPreorder.{0} X.Subcomplex
          (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            X))
        (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f)))
    (@Set.Icc_subset_Ico_right.{0} (Set.{0} X.Subcomplex)
      (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
            (Set.{0} X.Subcomplex)
            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
              (Set.{0} X.Subcomplex)
              (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                    (Set.{0} X.Subcomplex)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex))))))))
      (@Set.Iic.{0} X.Subcomplex
        (@PartialOrder.toPreorder.{0} X.Subcomplex
          (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            X))
        (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f))
      u v
      (@ssubset_of_ssubset_of_eq.{0} (Set.{0} X.Subcomplex)
        (Set.instUsesSetNotationForOrder.{0} X.Subcomplex) u
        (@lowerBounds.{0} X.Subcomplex
          (@Preorder.toLE.{0} X.Subcomplex
            (@PartialOrder.toPreorder.{0} X.Subcomplex
              (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                X)))
          (@Set.Icc.{0} X.Subcomplex
            (@PartialOrder.toPreorder.{0} X.Subcomplex
              (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                X))
            (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f) B))
        (@Set.Iic.{0} X.Subcomplex
          (@PartialOrder.toPreorder.{0} X.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              X))
          (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f))
        (@Preorder.toLT.{0} (Set.{0} X.Subcomplex)
          (@PartialOrder.toPreorder.{0} (Set.{0} X.Subcomplex)
            (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} X.Subcomplex)
              (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                (Set.{0} X.Subcomplex)
                (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                  (Set.{0} X.Subcomplex)
                  (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} X.Subcomplex)
                    (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} X.Subcomplex)
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                        (Set.{0} X.Subcomplex)
                        (@Set.instCompleteAtomicBooleanAlgebra.{0} X.Subcomplex)))))))))
        h_6
        (@lowerBounds_Icc.{0} X.Subcomplex
          (@PartialOrder.toPreorder.{0} X.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              X))
          B (@SSet.Subcomplex.image.{0} Y X (@SSet.Subcomplex.preimage.{0} X Y B f) f)
          (@SSet.Subcomplex.image_preimage_le.{0} X Y B f)))))
