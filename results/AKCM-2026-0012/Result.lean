import Mathlib.Algebra.Group.End
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Max
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Equiv.Perm.support_le_prod_of_mem (Equiv)
-- Step 1: ne_bot_mono (ne_bot_mono)
-- Step 6: eq_of_subset_of_not_ssubset (eq_of_subset_of_not_ssubset)
-- Step 7: superset_of_eq (superset_of_eq)
-- Step 8: sdiff_lt (sdiff_lt)
-- Step 9: ssubset_of_ssubset_of_subset (ssubset_of_ssubset_of_subset)
-- Step 10: not_isMin_of_lt (not_isMin_of_lt)
theorem akcm_2026_0012
    {α : Type}
    [inst_2 : DecidableEq.{1} α]
    [inst_3 : Fintype.{0} α]
    {f : Equiv.Perm.{1} α}
    {l : List.{0} (Equiv.Perm.{1} α)}
    (h : @Membership.mem.{0, 0} (Equiv.Perm.{1} α) (List.{0} (Equiv.Perm.{1} α))
  (@List.instMembership.{0} (Equiv.Perm.{1} α)) l f)
    (hl : @List.Pairwise.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.Disjoint.{0} α) l)
    (h_8 : @Ne.{1} (Finset.{0} α) (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
  (@Bot.bot.{0} (Finset.{0} α)
    (@OrderBot.toBot.{0} (Finset.{0} α)
      (@Preorder.toLE.{0} (Finset.{0} α)
        (@PartialOrder.toPreorder.{0} (Finset.{0} α)
          (@Finset.instPartialOrder.{0} α)))
      (@Finset.instOrderBot.{0} α))))
    (h_9 : Not
  (@LT.lt.{0} (Finset.{0} α)
    (@Preorder.toLT.{0} (Finset.{0} α)
      (@PartialOrder.toPreorder.{0} (Finset.{0} α)
        (@Finset.instPartialOrder.{0} α)))
    (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
    (@Equiv.Perm.support.{0} α inst_2 inst_3
      (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
        (@Equiv.Perm.instOne.{0} α) l)))) :
    Not
  (@IsMin.{0} (Finset.{0} α)
    (@Preorder.toLE.{0} (Finset.{0} α)
      (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
    (@Equiv.Perm.support.{0} α inst_2 inst_3
      (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
        (@Equiv.Perm.instOne.{0} α) l))) :=   @not_isMin_of_lt.{0} (Finset.{0} α)
  (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α))
  (@Equiv.Perm.support.{0} α inst_2 inst_3
    (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α) (@Equiv.Perm.instOne.{0} α)
      l))
  (@sdiff.{0} (Finset.{0} α)
    (@GeneralizedBooleanAlgebra.toSDiff.{0} (Finset.{0} α)
      (@Finset.instGeneralizedBooleanAlgebra.{0} α inst_2))
    (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
    (@Equiv.Perm.support.{0} α inst_2 inst_3
      (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α) (@Equiv.Perm.instOne.{0} α)
        l)))
  (@ssubset_of_ssubset_of_subset.{0} (Finset.{0} α) (Finset.instUsesSetNotationForOrder.{0} α)
    (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α))
    (@sdiff.{0} (Finset.{0} α)
      (@GeneralizedBooleanAlgebra.toSDiff.{0} (Finset.{0} α)
        (@Finset.instGeneralizedBooleanAlgebra.{0} α inst_2))
      (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
      (@Equiv.Perm.support.{0} α inst_2 inst_3
        (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
          (@Equiv.Perm.instOne.{0} α) l)))
    (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
    (@Equiv.Perm.support.{0} α inst_2 inst_3
      (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α) (@Equiv.Perm.instOne.{0} α)
        l))
    (@sdiff_lt.{0} (Finset.{0} α) (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
      (@Equiv.Perm.support.{0} α inst_2 inst_3
        (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
          (@Equiv.Perm.instOne.{0} α) l))
      (@Finset.instGeneralizedBooleanAlgebra.{0} α inst_2)
      (@superset_of_eq.{0} (Finset.{0} α) (Finset.instUsesSetNotationForOrder.{0} α)
        (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α))
        (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
        (@Equiv.Perm.support.{0} α inst_2 inst_3
          (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
            (@Equiv.Perm.instOne.{0} α) l))
        (@eq_of_subset_of_not_ssubset.{0} (Finset.{0} α)
          (Finset.instUsesSetNotationForOrder.{0} α) (@Finset.instPartialOrder.{0} α)
          (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
          (@Equiv.Perm.support.{0} α inst_2 inst_3
            (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
              (@Equiv.Perm.instOne.{0} α) l))
          (@Equiv.Perm.support_le_prod_of_mem.{0} α inst_2 inst_3 f l h hl) h_9))
      (@ne_bot_mono.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)
        (@Finset.instOrderBot.{0} α) (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
        (@Equiv.Perm.support.{0} α inst_2 inst_3
          (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
            (@Equiv.Perm.instOne.{0} α) l))
        (@Equiv.Perm.support_le_prod_of_mem.{0} α inst_2 inst_3 f l h hl) h_8))
    (@Equiv.Perm.support_le_prod_of_mem.{0} α inst_2 inst_3 f l h hl))
