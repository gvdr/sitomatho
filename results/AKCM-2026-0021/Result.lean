import Batteries.Data.List.Basic
import Batteries.Data.List.Perm
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.Language
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Notation

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: ContextFreeRule.Rewrites.append_left (ContextFreeRule)
-- Step 3: ContextFreeRule.Rewrites.append_right (ContextFreeRule)
-- Step 4: ContextFreeRule.Rewrites.nonterminal_input_mem (ContextFreeRule)
-- Step 5: List.cons_subperm_of_not_mem_of_mem (List)
-- Step 6: List.Subperm.countP_le (List)
-- Step 7: Set.notMem_Ioc_of_le (Set)
-- Step 8: Set.ssubset_insert (Set)
-- Step 9: LT.lt.ne_top (LT)
theorem akcm_2026_0021
    {T : Type}
    {N : Type}
    {r : ContextFreeRule.{0, 0} T N}
    {u : List.{0} (Symbol.{0, 0} T N)}
    {v : List.{0} (Symbol.{0, 0} T N)}
    (hvw : @ContextFreeRule.Rewrites.{0, 0} T N r u v)
    (p : List.{0} (Symbol.{0, 0} T N))
    {w : List.{0} (Symbol.{0, 0} T N)}
    (h_9 : @Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r) ∉ w)
    (h_10 : @List.Subperm.{0} (Symbol.{0, 0} T N) w
  (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
    (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
    (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
      (@List.instAppend.{0} (Symbol.{0, 0} T N)))
    (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
      (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
      (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
        (@List.instAppend.{0} (Symbol.{0, 0} T N)))
      p u)
    p))
    (a : Symbol.{0, 0} T N → Bool)
    {b : Nat} :
    @Ne.{1} (Set.{0} Nat)
  (@Set.Ioc.{0} Nat Nat.instPreorder
    (@List.countP.{0} (Symbol.{0, 0} T N) a
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
        (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
        (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
          (@List.instAppend.{0} (Symbol.{0, 0} T N)))
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
          (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
          (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
            (@List.instAppend.{0} (Symbol.{0, 0} T N)))
          p u)
        p))
    b)
  (@Top.top.{0} (Set.{0} Nat)
    (@OrderTop.toTop.{0} (Set.{0} Nat)
      (@Preorder.toLE.{0} (Set.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Set.{0} Nat)
          (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} Nat)
            (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} Nat)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} Nat) (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))))
      (@Set.instOrderTop.{0} Nat))) :=   @LT.lt.ne_top.{0} (Set.{0} Nat)
  (@PartialOrder.toPreorder.{0} (Set.{0} Nat)
    (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} Nat)
      (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} Nat)
        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
            (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat))))))
  (@Set.instOrderTop.{0} Nat)
  (@Set.Ioc.{0} Nat Nat.instPreorder
    (@List.countP.{0} (Symbol.{0, 0} T N) a
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
        (List.{0} (Symbol.{0, 0} T N))
        (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
          (@List.instAppend.{0} (Symbol.{0, 0} T N)))
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
          (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
          (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
            (@List.instAppend.{0} (Symbol.{0, 0} T N)))
          p u)
        p))
    b)
  (@insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
    (@List.countP.{0} (Symbol.{0, 0} T N) a
      (@List.cons.{0} (Symbol.{0, 0} T N)
        (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w))
    (@Set.Ioc.{0} Nat Nat.instPreorder
      (@List.countP.{0} (Symbol.{0, 0} T N) a
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
          (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
          (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
            (@List.instAppend.{0} (Symbol.{0, 0} T N)))
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
            (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
            (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
              (@List.instAppend.{0} (Symbol.{0, 0} T N)))
            p u)
          p))
      b))
  (@Set.ssubset_insert.{0} Nat
    (@Set.Ioc.{0} Nat Nat.instPreorder
      (@List.countP.{0} (Symbol.{0, 0} T N) a
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
          (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
          (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
            (@List.instAppend.{0} (Symbol.{0, 0} T N)))
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
            (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
            (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
              (@List.instAppend.{0} (Symbol.{0, 0} T N)))
            p u)
          p))
      b)
    (@List.countP.{0} (Symbol.{0, 0} T N) a
      (@List.cons.{0} (Symbol.{0, 0} T N)
        (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w))
    (@Set.notMem_Ioc_of_le.{0} Nat Nat.instPreorder
      (@List.countP.{0} (Symbol.{0, 0} T N) a
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
          (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
          (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
            (@List.instAppend.{0} (Symbol.{0, 0} T N)))
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
            (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
            (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
              (@List.instAppend.{0} (Symbol.{0, 0} T N)))
            p u)
          p))
      b
      (@List.countP.{0} (Symbol.{0, 0} T N) a
        (@List.cons.{0} (Symbol.{0, 0} T N)
          (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w))
      (@List.Subperm.countP_le.{0} (Symbol.{0, 0} T N) a
        (@List.cons.{0} (Symbol.{0, 0} T N)
          (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w)
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
          (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
          (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
            (@List.instAppend.{0} (Symbol.{0, 0} T N)))
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
            (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
            (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
              (@List.instAppend.{0} (Symbol.{0, 0} T N)))
            p u)
          p)
        (@List.cons_subperm_of_not_mem_of_mem.{0} (Symbol.{0, 0} T N)
          (@Symbol.nonterminal.{0, 0} T N (@ContextFreeRule.input.{0, 0} T N r)) w
          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
            (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
            (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
              (@List.instAppend.{0} (Symbol.{0, 0} T N)))
            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
              (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
              (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
                (@List.instAppend.{0} (Symbol.{0, 0} T N)))
              p u)
            p)
          h_9
          (@ContextFreeRule.Rewrites.nonterminal_input_mem.{0, 0} T N r
            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
              (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
              (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
                (@List.instAppend.{0} (Symbol.{0, 0} T N)))
              (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
                (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
                (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
                  (@List.instAppend.{0} (Symbol.{0, 0} T N)))
                p u)
              p)
            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
              (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
              (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
                (@List.instAppend.{0} (Symbol.{0, 0} T N)))
              (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
                (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
                (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
                  (@List.instAppend.{0} (Symbol.{0, 0} T N)))
                p v)
              p)
            (@ContextFreeRule.Rewrites.append_right.{0, 0} T N r
              (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
                (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
                (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
                  (@List.instAppend.{0} (Symbol.{0, 0} T N)))
                p u)
              (@HAppend.hAppend.{0, 0, 0} (List.{0} (Symbol.{0, 0} T N))
                (List.{0} (Symbol.{0, 0} T N)) (List.{0} (Symbol.{0, 0} T N))
                (@instHAppendOfAppend.{0} (List.{0} (Symbol.{0, 0} T N))
                  (@List.instAppend.{0} (Symbol.{0, 0} T N)))
                p v)
              (@ContextFreeRule.Rewrites.append_left.{0, 0} T N r u v hvw p) p))
          h_10))))
