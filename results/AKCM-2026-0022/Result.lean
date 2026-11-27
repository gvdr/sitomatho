import Batteries.Data.List.Basic
import Batteries.Data.List.Perm
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.Language
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: ContextFreeRule.Rewrites.nonterminal_input_mem (ContextFreeRule)
-- Step 1: List.cons_subperm_of_not_mem_of_mem (List)
-- Step 2: List.Subperm.countP_le (List)
-- Step 3: isLUB_Icc (isLUB_Icc)
-- Step 4: IsLUB.unique (IsLUB)
-- Step 8: dvd_of_eq (dvd_of_eq)
-- Step 9: exists_eq_mul_left_of_dvd (exists_eq_mul_left_of_dvd)
theorem akcm_2026_0022
    {T : Type}
    {N : Type}
    {r : ContextFreeRule.{0, 0} T N}
    {u : List.{0} (Symbol.{0, 0} T N)}
    {v : List.{0} (Symbol.{0, 0} T N)}
    (h_6 : @ContextFreeRule.Rewrites.{0, 0} T N r u v)
    {w : List.{0} (Symbol.{0, 0} T N)}
    (h_8 : @Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r) ∉ w)
    (h_9 : @List.Subperm.{0} (Symbol.{0, 0} T N) w u)
    (a : Symbol.{0, 0} T N → Bool)
    {b : Nat}
    (h_12 : @IsLUB.{0} Nat
  (@Preorder.toLE.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder))
  (@Set.Icc.{0} Nat Nat.instPreorder
    (@List.countP.{0} (Symbol.{0, 0} T N) a
      (@List.cons.{0} (Symbol.{0, 0} T N)
        (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w))
    (@List.countP.{0} (Symbol.{0, 0} T N) a u))
  b) :
    ∃ c,
  @Eq.{1} Nat b
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
      (@instHMul.{0} Nat
        (@CommMagma.toMul.{0} Nat
          (@CommSemigroup.toCommMagma.{0} Nat Nat.instCommSemigroup)))
      c (@List.countP.{0} (Symbol.{0, 0} T N) a u)) :=   @exists_eq_mul_left_of_dvd.{0} Nat Nat.instCommSemigroup
  (@List.countP.{0} (Symbol.{0, 0} T N) a u) b
  (@dvd_of_eq.{0} Nat Nat.instMonoid (@List.countP.{0} (Symbol.{0, 0} T N) a u) b
    (@IsLUB.unique.{0} Nat Nat.instPartialOrder
      (@Set.Icc.{0} Nat Nat.instPreorder
        (@List.countP.{0} (Symbol.{0, 0} T N) a
          (@List.cons.{0} (Symbol.{0, 0} T N)
            (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w))
        (@List.countP.{0} (Symbol.{0, 0} T N) a u))
      (@List.countP.{0} (Symbol.{0, 0} T N) a u) b
      (@isLUB_Icc.{0} Nat Nat.instPreorder
        (@List.countP.{0} (Symbol.{0, 0} T N) a
          (@List.cons.{0} (Symbol.{0, 0} T N)
            (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w))
        (@List.countP.{0} (Symbol.{0, 0} T N) a u)
        (@List.Subperm.countP_le.{0} (Symbol.{0, 0} T N) a
          (@List.cons.{0} (Symbol.{0, 0} T N)
            (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w)
          u
          (@List.cons_subperm_of_not_mem_of_mem.{0} (Symbol.{0, 0} T N)
            (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w u h_8
            (@ContextFreeRule.Rewrites.nonterminal_input_mem.{0, 0} T N r u v h_6) h_9)))
      h_12))
