import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Opposite
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.RelClasses

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: SSet.relativeCellComplexOfMono.Cell.range_map_le (SSet)
-- Step 3: Set.Icc_ssubset_Icc_left (Set)
-- Step 4: not_subset_of_ssubset (not_subset_of_ssubset)
-- Step 5: ne_of_not_subset (ne_of_not_subset)
-- Step 6: Set.nontrivial_pair (Set)
-- Step 7: Set.Nontrivial.pair_subset (Set)
theorem akcm_2026_0009
    {X : SSet.{0}}
    {Y : SSet.{0}}
    {i : @Quiver.Hom.{0, 1} SSet.{0}
  (@CategoryTheory.CategoryStruct.toQuiver.{0, 1} SSet.{0}
    (@CategoryTheory.Category.toCategoryStruct.{0, 1} SSet.{0}
      (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        Type CategoryTheory.types.{0})))
  X Y}
    {d : Nat}
    (c : @SSet.relativeCellComplexOfMono.Cell.{0} X Y i d)
    {u : Y.Subcomplex}
    {v : Y.Subcomplex}
    (h_8 : @LT.lt.{0} Y.Subcomplex
  (@Preorder.toLT.{0} Y.Subcomplex
    (@PartialOrder.toPreorder.{0} Y.Subcomplex
      (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
        (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        Y)))
  (@SSet.Subcomplex.range.{0}
    (@CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory
      SimplexCategory.smallCategory SSet.{0}
      (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        Type CategoryTheory.types.{0})
      SSet.stdSimplex.{0} { len := d })
    Y (@SSet.relativeCellComplexOfMono.Cell.map.{0} X Y i d c))
  u)
    (h_9 : @LE.le.{0} Y.Subcomplex
  (@Preorder.toLE.{0} Y.Subcomplex
    (@PartialOrder.toPreorder.{0} Y.Subcomplex
      (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
        (Opposite.{1} SimplexCategory)
        (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
          SimplexCategory.smallCategory)
        Y)))
  v
  (@DFunLike.coe.{1, 1, 1}
    (@OrderHom.{0, 0} Nat Y.Subcomplex Nat.instPreorder
      (@PartialOrder.toPreorder.{0} Y.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
          (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          Y)))
    Nat (fun x ↦ Y.Subcomplex)
    (@OrderHom.instFunLike.{0, 0} Nat Y.Subcomplex Nat.instPreorder
      (@PartialOrder.toPreorder.{0} Y.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
          (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          Y)))
    (@SSet.skeletonOfMono.{0} X Y i)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) :
    ∃ x y,
  And (@Ne.{1} (Set.{0} Y.Subcomplex) x y)
    (@LE.le.{0} (Set.{0} (Set.{0} Y.Subcomplex))
      (@Set.instLE.{0} (Set.{0} Y.Subcomplex))
      (@insert.{0, 0} (Set.{0} Y.Subcomplex) (Set.{0} (Set.{0} Y.Subcomplex))
        (@Set.instInsert.{0} (Set.{0} Y.Subcomplex)) x
        (@singleton.{0, 0} (Set.{0} Y.Subcomplex) (Set.{0} (Set.{0} Y.Subcomplex))
          (@Set.instSingletonSet.{0} (Set.{0} Y.Subcomplex)) y))
      (@insert.{0, 0} (Set.{0} Y.Subcomplex) (Set.{0} (Set.{0} Y.Subcomplex))
        (@Set.instInsert.{0} (Set.{0} Y.Subcomplex))
        (@Set.Icc.{0} Y.Subcomplex
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
              (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y))
          (@SSet.Subcomplex.range.{0}
            (@CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory
              SimplexCategory.smallCategory SSet.{0}
              (@CategoryTheory.Functor.category.{0, 0, 0, 1}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                Type CategoryTheory.types.{0})
              SSet.stdSimplex.{0} { len := d })
            Y (@SSet.relativeCellComplexOfMono.Cell.map.{0} X Y i d c))
          (@DFunLike.coe.{1, 1, 1}
            (@OrderHom.{0, 0} Nat Y.Subcomplex Nat.instPreorder
              (@PartialOrder.toPreorder.{0} Y.Subcomplex
                (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  Y)))
            Nat (fun x ↦ Y.Subcomplex)
            (@OrderHom.instFunLike.{0, 0} Nat Y.Subcomplex Nat.instPreorder
              (@PartialOrder.toPreorder.{0} Y.Subcomplex
                (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  Y)))
            (@SSet.skeletonOfMono.{0} X Y i)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@singleton.{0, 0} (Set.{0} Y.Subcomplex) (Set.{0} (Set.{0} Y.Subcomplex))
          (@Set.instSingletonSet.{0} (Set.{0} Y.Subcomplex))
          (@Set.Icc.{0} Y.Subcomplex
            (@PartialOrder.toPreorder.{0} Y.Subcomplex
              (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                Y))
            u v)))) :=   @Set.Nontrivial.pair_subset.{0} (Set.{0} Y.Subcomplex)
  (@insert.{0, 0} (Set.{0} Y.Subcomplex) (Set.{0} (Set.{0} Y.Subcomplex))
    (@Set.instInsert.{0} (Set.{0} Y.Subcomplex))
    (@Set.Icc.{0} Y.Subcomplex
      (@PartialOrder.toPreorder.{0} Y.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          Y))
      (@SSet.Subcomplex.range.{0}
        (@CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory
          SSet.{0}
          (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            Type CategoryTheory.types.{0})
          SSet.stdSimplex.{0} { len := d })
        Y (@SSet.relativeCellComplexOfMono.Cell.map.{0} X Y i d c))
      (@DFunLike.coe.{1, 1, 1}
        (@OrderHom.{0, 0} Nat Y.Subcomplex Nat.instPreorder
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y)))
        Nat (fun x ↦ Y.Subcomplex)
        (@OrderHom.instFunLike.{0, 0} Nat Y.Subcomplex Nat.instPreorder
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y)))
        (@SSet.skeletonOfMono.{0} X Y i)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@singleton.{0, 0} (Set.{0} Y.Subcomplex) (Set.{0} (Set.{0} Y.Subcomplex))
      (@Set.instSingletonSet.{0} (Set.{0} Y.Subcomplex))
      (@Set.Icc.{0} Y.Subcomplex
        (@PartialOrder.toPreorder.{0} Y.Subcomplex
          (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            Y))
        u v)))
  (@Set.nontrivial_pair.{0} (Set.{0} Y.Subcomplex)
    (@Set.Icc.{0} Y.Subcomplex
      (@PartialOrder.toPreorder.{0} Y.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          Y))
      (@SSet.Subcomplex.range.{0}
        (@CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory SimplexCategory.smallCategory
          SSet.{0}
          (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            Type CategoryTheory.types.{0})
          SSet.stdSimplex.{0} { len := d })
        Y (@SSet.relativeCellComplexOfMono.Cell.map.{0} X Y i d c))
      (@DFunLike.coe.{1, 1, 1}
        (@OrderHom.{0, 0} Nat Y.Subcomplex Nat.instPreorder
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y)))
        Nat (fun x ↦ Y.Subcomplex)
        (@OrderHom.instFunLike.{0, 0} Nat Y.Subcomplex Nat.instPreorder
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y)))
        (@SSet.skeletonOfMono.{0} X Y i)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@Set.Icc.{0} Y.Subcomplex
      (@PartialOrder.toPreorder.{0} Y.Subcomplex
        (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
          (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
            SimplexCategory.smallCategory)
          Y))
      u v)
    (@ne_of_not_subset.{0} (Set.{0} Y.Subcomplex)
      (Set.instUsesSetNotationForOrder.{0} Y.Subcomplex)
      (@PartialOrder.toPreorder.{0} (Set.{0} Y.Subcomplex)
        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} Y.Subcomplex)
          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
            (Set.{0} Y.Subcomplex)
            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
              (Set.{0} Y.Subcomplex)
              (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} Y.Subcomplex)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Y.Subcomplex)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                    (Set.{0} Y.Subcomplex)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} Y.Subcomplex))))))))
      (@Set.Icc.{0} Y.Subcomplex
        (@PartialOrder.toPreorder.{0} Y.Subcomplex
          (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            Y))
        (@SSet.Subcomplex.range.{0}
          (@CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory
            SimplexCategory.smallCategory SSet.{0}
            (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Type CategoryTheory.types.{0})
            SSet.stdSimplex.{0} { len := d })
          Y (@SSet.relativeCellComplexOfMono.Cell.map.{0} X Y i d c))
        (@DFunLike.coe.{1, 1, 1}
          (@OrderHom.{0, 0} Nat Y.Subcomplex Nat.instPreorder
            (@PartialOrder.toPreorder.{0} Y.Subcomplex
              (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                Y)))
          Nat (fun x ↦ Y.Subcomplex)
          (@OrderHom.instFunLike.{0, 0} Nat Y.Subcomplex Nat.instPreorder
            (@PartialOrder.toPreorder.{0} Y.Subcomplex
              (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                Y)))
          (@SSet.skeletonOfMono.{0} X Y i)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Set.Icc.{0} Y.Subcomplex
        (@PartialOrder.toPreorder.{0} Y.Subcomplex
          (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
            (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
              SimplexCategory.smallCategory)
            Y))
        u v)
      (@not_subset_of_ssubset.{0} (Set.{0} Y.Subcomplex)
        (Set.instUsesSetNotationForOrder.{0} Y.Subcomplex)
        (@PartialOrder.toPreorder.{0} (Set.{0} Y.Subcomplex)
          (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} (Set.{0} Y.Subcomplex)
            (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
              (Set.{0} Y.Subcomplex)
              (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                (Set.{0} Y.Subcomplex)
                (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} Y.Subcomplex)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Y.Subcomplex)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                      (Set.{0} Y.Subcomplex)
                      (@Set.instCompleteAtomicBooleanAlgebra.{0} Y.Subcomplex))))))))
        (@Set.Icc.{0} Y.Subcomplex
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y))
          u v)
        (@Set.Icc.{0} Y.Subcomplex
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y))
          (@SSet.Subcomplex.range.{0}
            (@CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory
              SimplexCategory.smallCategory SSet.{0}
              (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                Type CategoryTheory.types.{0})
              SSet.stdSimplex.{0} { len := d })
            Y (@SSet.relativeCellComplexOfMono.Cell.map.{0} X Y i d c))
          (@DFunLike.coe.{1, 1, 1}
            (@OrderHom.{0, 0} Nat Y.Subcomplex Nat.instPreorder
              (@PartialOrder.toPreorder.{0} Y.Subcomplex
                (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  Y)))
            Nat (fun x ↦ Y.Subcomplex)
            (@OrderHom.instFunLike.{0, 0} Nat Y.Subcomplex Nat.instPreorder
              (@PartialOrder.toPreorder.{0} Y.Subcomplex
                (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  Y)))
            (@SSet.skeletonOfMono.{0} X Y i)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Set.Icc_ssubset_Icc_left.{0} Y.Subcomplex
          (@PartialOrder.toPreorder.{0} Y.Subcomplex
            (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0} (Opposite.{1} SimplexCategory)
              (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                SimplexCategory.smallCategory)
              Y))
          u
          (@SSet.Subcomplex.range.{0}
            (@CategoryTheory.Functor.obj.{0, 0, 0, 1} SimplexCategory
              SimplexCategory.smallCategory SSet.{0}
              (@CategoryTheory.Functor.category.{0, 0, 0, 1} (Opposite.{1} SimplexCategory)
                (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                  SimplexCategory.smallCategory)
                Type CategoryTheory.types.{0})
              SSet.stdSimplex.{0} { len := d })
            Y (@SSet.relativeCellComplexOfMono.Cell.map.{0} X Y i d c))
          v
          (@DFunLike.coe.{1, 1, 1}
            (@OrderHom.{0, 0} Nat Y.Subcomplex Nat.instPreorder
              (@PartialOrder.toPreorder.{0} Y.Subcomplex
                (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  Y)))
            Nat (fun x ↦ Y.Subcomplex)
            (@OrderHom.instFunLike.{0, 0} Nat Y.Subcomplex Nat.instPreorder
              (@PartialOrder.toPreorder.{0} Y.Subcomplex
                (@CategoryTheory.instPartialOrderSubfunctor.{0, 0, 0}
                  (Opposite.{1} SimplexCategory)
                  (@CategoryTheory.Category.opposite.{0, 0} SimplexCategory
                    SimplexCategory.smallCategory)
                  Y)))
            (@SSet.skeletonOfMono.{0} X Y i)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@SSet.relativeCellComplexOfMono.Cell.range_map_le.{0} X Y i d c) h_8 h_9))))
