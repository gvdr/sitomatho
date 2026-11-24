import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.RelClasses
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.UpperLower.CompleteLattice

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: IsUpperSet.ordConnected (IsUpperSet)
-- Step 1: Set.OrdConnected.upperClosure_inter_lowerClosure (Set)
-- Step 2: superset_of_eq (superset_of_eq)
-- Step 5: ssubset_of_ssubset_of_eq (ssubset_of_ssubset_of_eq)
-- Step 6: LT.lt.trans_subset (LT)
-- Step 10: Set.nonempty_of_ssubset (Set)
-- Step 11: Set.Nonempty.coe_sort (Set)
theorem akcm_2026_0011
    {α : Type}
    [inst_2 : Preorder.{0} α]
    {s : Set.{0} α}
    (h : @IsUpperSet.{0} α (@Preorder.toLE.{0} α inst_2) s)
    {u : Set.{0} α}
    (h_6 : @LT.lt.{0} (Set.{0} α)
  (@Preorder.toLT.{0} (Set.{0} α)
    (@PartialOrder.toPreorder.{0} (Set.{0} α)
      (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
        (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
              (@Set.instCompleteAtomicBooleanAlgebra.{0} α)))))))
  u
  (@min.{0} (Set.{0} α) (@Set.instMin.{0} α)
    (@SetLike.coe.{0, 0} (@UpperSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
      (@UpperSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
      (@upperClosure.{0} α inst_2 s))
    (@SetLike.coe.{0, 0} (@LowerSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
      (@LowerSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
      (@lowerClosure.{0} α inst_2 s)))) :
    Nonempty.{1}
  (@Set.Elem.{0} α
    (@sdiff.{0} (Set.{0} α) (@Set.instSDiff.{0} α)
      (@min.{0} (Set.{0} α) (@Set.instMin.{0} α)
        (@SetLike.coe.{0, 0} (@UpperSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
          (@UpperSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
          (@upperClosure.{0} α inst_2 s))
        (@SetLike.coe.{0, 0} (@LowerSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
          (@LowerSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
          (@lowerClosure.{0} α inst_2 s)))
      u)) :=   @Set.Nonempty.coe_sort.{0} α
  (@sdiff.{0} (Set.{0} α) (@Set.instSDiff.{0} α)
    (@min.{0} (Set.{0} α) (@Set.instMin.{0} α)
      (@SetLike.coe.{0, 0} (@UpperSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
        (@UpperSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
        (@upperClosure.{0} α inst_2 s))
      (@SetLike.coe.{0, 0} (@LowerSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
        (@LowerSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
        (@lowerClosure.{0} α inst_2 s)))
    u)
  (@Set.nonempty_of_ssubset.{0} α u
    (@min.{0} (Set.{0} α) (@Set.instMin.{0} α)
      (@SetLike.coe.{0, 0} (@UpperSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
        (@UpperSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
        (@upperClosure.{0} α inst_2 s))
      (@SetLike.coe.{0, 0} (@LowerSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
        (@LowerSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
        (@lowerClosure.{0} α inst_2 s)))
    (@LT.lt.trans_subset.{0} (Set.{0} α) (Set.instUsesSetNotationForOrder.{0} α)
      (@PartialOrder.toPreorder.{0} (Set.{0} α)
        (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
          (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
      u s
      (@min.{0} (Set.{0} α) (@Set.instMin.{0} α)
        (@SetLike.coe.{0, 0} (@UpperSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
          (@UpperSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
          (@upperClosure.{0} α inst_2 s))
        (@SetLike.coe.{0, 0} (@LowerSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
          (@LowerSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
          (@lowerClosure.{0} α inst_2 s)))
      (@ssubset_of_ssubset_of_eq.{0} (Set.{0} α) (Set.instUsesSetNotationForOrder.{0} α) u
        (@min.{0} (Set.{0} α) (@Set.instMin.{0} α)
          (@SetLike.coe.{0, 0} (@UpperSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
            (@UpperSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
            (@upperClosure.{0} α inst_2 s))
          (@SetLike.coe.{0, 0} (@LowerSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
            (@LowerSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
            (@lowerClosure.{0} α inst_2 s)))
        s
        (@Preorder.toLT.{0} (Set.{0} α)
          (@PartialOrder.toPreorder.{0} (Set.{0} α)
            (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
              (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
                (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
                  (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                    (@Set.instCompleteAtomicBooleanAlgebra.{0} α)))))))
        h_6
        (@Set.OrdConnected.upperClosure_inter_lowerClosure.{0} α inst_2 s
          (@IsUpperSet.ordConnected.{0} α inst_2 s h)))
      (@superset_of_eq.{0} (Set.{0} α) (Set.instUsesSetNotationForOrder.{0} α)
        (@PartialOrder.toPreorder.{0} (Set.{0} α)
          (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} α)
            (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} α)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} α)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} α)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} α))))))
        (@min.{0} (Set.{0} α) (@Set.instMin.{0} α)
          (@SetLike.coe.{0, 0} (@UpperSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
            (@UpperSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
            (@upperClosure.{0} α inst_2 s))
          (@SetLike.coe.{0, 0} (@LowerSet.{0} α (@Preorder.toLE.{0} α inst_2)) α
            (@LowerSet.instSetLike.{0} α (@Preorder.toLE.{0} α inst_2))
            (@lowerClosure.{0} α inst_2 s)))
        s
        (@Set.OrdConnected.upperClosure_inter_lowerClosure.{0} α inst_2 s
          (@IsUpperSet.ordConnected.{0} α inst_2 s h)))))
