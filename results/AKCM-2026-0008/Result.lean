import Mathlib.Algebra.Group.End
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Max
import Mathlib.Order.Notation

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Equiv.Perm.support_le_prod_of_mem (Equiv)
-- Step 2: Equiv.Perm.Disjoint.mono (Equiv)
-- Step 3: Equiv.Perm.Disjoint.disjoint_support (Equiv)
-- Step 4: Disjoint.ne_top_of_ne_bot (Disjoint)
-- Step 5: Ne.lt_top (Ne)
-- Step 6: LT.lt.not_isMax (LT)
theorem akcm_2026_0008
    {α : Type}
    [inst_2 : DecidableEq.{1} α]
    [inst_3 : Fintype.{0} α]
    {f : Equiv.Perm.{1} α}
    {l : List.{0} (Equiv.Perm.{1} α)}
    (h : @Membership.mem.{0, 0} (Equiv.Perm.{1} α) (List.{0} (Equiv.Perm.{1} α))
  (@List.instMembership.{0} (Equiv.Perm.{1} α)) l f)
    (hl : @List.Pairwise.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.Disjoint.{0} α) l)
    {u : Equiv.Perm.{1} α}
    {v : Equiv.Perm.{1} α}
    (h_10 : @Equiv.Perm.Disjoint.{0} α
  (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
    (@Equiv.Perm.instOne.{0} α) l)
  u)
    (h_11 : @LE.le.{0} (Finset.{0} α)
  (@Preorder.toLE.{0} (Finset.{0} α)
    (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
  (@Equiv.Perm.support.{0} α inst_2 inst_3 v)
  (@Equiv.Perm.support.{0} α inst_2 inst_3 u))
    (h_12 : @Ne.{1} (Finset.{0} α) (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
  (@Bot.bot.{0} (Finset.{0} α)
    (@OrderBot.toBot.{0} (Finset.{0} α)
      (@Preorder.toLE.{0} (Finset.{0} α)
        (@PartialOrder.toPreorder.{0} (Finset.{0} α)
          (@Finset.instPartialOrder.{0} α)))
      (@BoundedOrder.toOrderBot.{0} (Finset.{0} α)
        (@Preorder.toLE.{0} (Finset.{0} α)
          (@PartialOrder.toPreorder.{0} (Finset.{0} α)
            (@Finset.instPartialOrder.{0} α)))
        (@Finset.boundedOrder.{0} α inst_3))))) :
    Not
  (@IsMax.{0} (Finset.{0} α)
    (@Preorder.toLE.{0} (Finset.{0} α)
      (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
    (@Equiv.Perm.support.{0} α inst_2 inst_3 v)) :=   @LT.lt.not_isMax.{0} (Finset.{0} α)
  (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α))
  (@Equiv.Perm.support.{0} α inst_2 inst_3 v)
  (@Top.top.{0} (Finset.{0} α)
    (@OrderTop.toTop.{0} (Finset.{0} α)
      (@Preorder.toLE.{0} (Finset.{0} α)
        (@PartialOrder.toPreorder.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)))
      (@CoheytingAlgebra.toOrderTop.{0} (Finset.{0} α)
        (@BiheytingAlgebra.toCoheytingAlgebra.{0} (Finset.{0} α)
          (@BooleanAlgebra.toBiheytingAlgebra.{0} (Finset.{0} α)
            (@Finset.booleanAlgebra.{0} α inst_3 inst_2))))))
  (@Ne.lt_top.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)
    (@CoheytingAlgebra.toOrderTop.{0} (Finset.{0} α)
      (@BiheytingAlgebra.toCoheytingAlgebra.{0} (Finset.{0} α)
        (@BooleanAlgebra.toBiheytingAlgebra.{0} (Finset.{0} α)
          (@Finset.booleanAlgebra.{0} α inst_3 inst_2))))
    (@Equiv.Perm.support.{0} α inst_2 inst_3 v)
    (@Disjoint.ne_top_of_ne_bot.{0} (Finset.{0} α) (@Finset.instPartialOrder.{0} α)
      (@Finset.boundedOrder.{0} α inst_3) (@Equiv.Perm.support.{0} α inst_2 inst_3 f)
      (@Equiv.Perm.support.{0} α inst_2 inst_3 v)
      (@Equiv.Perm.Disjoint.disjoint_support.{0} α inst_2 inst_3 f v
        (@Equiv.Perm.Disjoint.mono.{0} α inst_2 inst_3
          (@List.prod.{0} (Equiv.Perm.{1} α) (@Equiv.Perm.instMul.{0} α)
            (@Equiv.Perm.instOne.{0} α) l)
          u f v h_10 (@Equiv.Perm.support_le_prod_of_mem.{0} α inst_2 inst_3 f l h hl) h_11))
      h_12))
