import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Operations
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Nat
import Mathlib.Order.Notation

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: RootPairing.rootSpan_ne_bot (RootPairing)
-- Step 2: Multiset.count_cons_of_ne (Multiset)
-- Step 3: dvd_of_eq (dvd_of_eq)
-- Step 8: IsRelPrime.isUnit_of_dvd (IsRelPrime)
-- Step 9: IsUnit.mul_left_injective (IsUnit)
-- Step 10: Function.Injective.nat_tendsto_atTop (Function)
-- Step 11: Filter.not_bddAbove_of_tendsto_atTop (Filter)
theorem akcm_2026_0020
    {ι : Type}
    {R : Type}
    {M : Type}
    {N : Type}
    [inst_5 : CommRing.{0} R]
    [inst_6 : AddCommGroup.{0} M]
    [inst_7 : @Module.{0, 0} R M
  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_5))
  (@AddCommGroup.toAddCommMonoid.{0} M inst_6)]
    [inst_8 : AddCommGroup.{0} N]
    [inst_9 : @Module.{0, 0} R N
  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_5))
  (@AddCommGroup.toAddCommMonoid.{0} N inst_8)]
    (P : @RootPairing.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9)
    (S : Type)
    [inst_12 : CommRing.{0} S]
    [inst_13 : @Module.{0, 0} S M
  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
  (@AddCommGroup.toAddCommMonoid.{0} M inst_6)]
    [inst_14 : Nonempty.{1} ι]
    [inst_15 : @NeZero.{0} R
  (@MulZeroClass.toZero.{0} R
    (@instMulZeroClassOfSemiring.{0} R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_5))))
  (@OfNat.ofNat.{0} R (nat_lit 2)
    (@instOfNatAtLeastTwo.{0} R (nat_lit 2)
      (@AddMonoidWithOne.toNatCast.{0} R
        (@AddGroupWithOne.toAddMonoidWithOne.{0} R
          (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_5))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Nat.instNeZeroSucc
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))]
    (u : Multiset.{0}
  (@Submodule.{0, 0} S M
    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
    (h_17 : @IsRelPrime.{0} Nat (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)
  (@Multiset.count.{0}
    (@Submodule.{0, 0} S M
      (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
      (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
    (@Submodule.decidableEq.{0, 0} S M
      (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
      (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
    (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
      inst_9 P S inst_12 inst_13)
    (@Multiset.cons.{0}
      (@Submodule.{0, 0} S M
        (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
        (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
      (@Bot.bot.{0}
        (@Submodule.{0, 0} S M
          (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
          (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
        (@Submodule.instBot.{0, 0} S M
          (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
          (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
      u))
  (@Multiset.count.{0}
    (@Submodule.{0, 0} S M
      (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
      (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
    (@Submodule.decidableEq.{0, 0} S M
      (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
      (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
    (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
      inst_9 P S inst_12 inst_13)
    u)) :
    Not
  (@BddAbove.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
    (@Set.range.{0, 1} Nat Nat fun x ↦
      @HMul.hMul.{0, 0, 0} Nat Nat Nat
        (@instHMul.{0} Nat
          (@MulOne.toMul.{0} Nat
            (@MulOneClass.toMulOne.{0} Nat
              (@Monoid.toMulOneClass.{0} Nat
                (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)))))
        x
        (@Multiset.count.{0}
          (@Submodule.{0, 0} S M
            (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
            (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
          (@Submodule.decidableEq.{0, 0} S M
            (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
            (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
          (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
            inst_9 P S inst_12 inst_13)
          (@Multiset.cons.{0}
            (@Submodule.{0, 0} S M
              (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
              (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
            (@Bot.bot.{0}
              (@Submodule.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S
                  (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@Submodule.instBot.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S
                  (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
            u)))) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Filter.not_bddAbove_of_tendsto_atTop.{0, 0} Nat Nat Nat.instPreorder
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@Filter.atTop_neBot.{0} Nat Nat.instPreorder
        (@instIsDirectedOrder.{0} Nat Nat.instSemiring Nat.instPartialOrder
          (@IsStrictOrderedRing.toIsOrderedRing.{0} Nat Nat.instSemiring Nat.instPartialOrder
            Nat.instIsStrictOrderedRing)
          instArchimedeanNat)
        (@instNonemptyOfInhabited.{1} Nat instInhabitedNat))
      (fun x ↦
        @HMul.hMul.{0, 0, 0} Nat Nat Nat
          (@instHMul.{0} Nat
            (@MulOne.toMul.{0} Nat
              (@MulOneClass.toMulOne.{0} Nat
                (@Monoid.toMulOneClass.{0} Nat (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)))))
          x
          (@Multiset.count.{0}
            (@Submodule.{0, 0} S M
              (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
              (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
            (@Submodule.decidableEq.{0, 0} S M
              (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
              (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
            (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P S
              inst_12 inst_13)
            (@Multiset.cons.{0}
              (@Submodule.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@Bot.bot.{0}
                (@Submodule.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@Submodule.instBot.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
              u)))
      Nat.instNoMaxOrder
      (@Function.Injective.nat_tendsto_atTop
        (fun x ↦
          @HMul.hMul.{0, 0, 0} Nat Nat Nat
            (@instHMul.{0} Nat
              (@MulOne.toMul.{0} Nat
                (@MulOneClass.toMulOne.{0} Nat
                  (@Monoid.toMulOneClass.{0} Nat
                    (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)))))
            x
            (@Multiset.count.{0}
              (@Submodule.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@Submodule.decidableEq.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P S
                inst_12 inst_13)
              (@Multiset.cons.{0}
                (@Submodule.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@Bot.bot.{0}
                  (@Submodule.{0, 0} S M
                    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                  (@Submodule.instBot.{0, 0} S M
                    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
                u)))
        (@IsUnit.mul_left_injective.{0} Nat (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)
          (@Multiset.count.{0}
            (@Submodule.{0, 0} S M
              (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
              (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
            (@Submodule.decidableEq.{0, 0} S M
              (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
              (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
            (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P S
              inst_12 inst_13)
            (@Multiset.cons.{0}
              (@Submodule.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@Bot.bot.{0}
                (@Submodule.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@Submodule.instBot.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
              u))
          (@IsRelPrime.isUnit_of_dvd.{0} Nat Nat.instCommMonoid
            (@Multiset.count.{0}
              (@Submodule.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@Submodule.decidableEq.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P S
                inst_12 inst_13)
              (@Multiset.cons.{0}
                (@Submodule.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@Bot.bot.{0}
                  (@Submodule.{0, 0} S M
                    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                  (@Submodule.instBot.{0, 0} S M
                    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
                u))
            (@Multiset.count.{0}
              (@Submodule.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@Submodule.decidableEq.{0, 0} S M
                (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
              (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P S
                inst_12 inst_13)
              u)
            h_17
            (@dvd_of_eq.{0} Nat Nat.instMonoid
              (@Multiset.count.{0}
                (@Submodule.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@Submodule.decidableEq.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P
                  S inst_12 inst_13)
                (@Multiset.cons.{0}
                  (@Submodule.{0, 0} S M
                    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                  (@Bot.bot.{0}
                    (@Submodule.{0, 0} S M
                      (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                      (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                    (@Submodule.instBot.{0, 0} S M
                      (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                      (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
                  u))
              (@Multiset.count.{0}
                (@Submodule.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@Submodule.decidableEq.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P
                  S inst_12 inst_13)
                u)
              (@Multiset.count_cons_of_ne.{0}
                (@Submodule.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@Submodule.decidableEq.{0, 0} S M
                  (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                  (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                (@RootPairing.rootSpan.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P
                  S inst_12 inst_13)
                (@Bot.bot.{0}
                  (@Submodule.{0, 0} S M
                    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13)
                  (@Submodule.instBot.{0, 0} S M
                    (@CommSemiring.toSemiring.{0} S (@CommRing.toCommSemiring.{0} S inst_12))
                    (@AddCommGroup.toAddCommMonoid.{0} M inst_6) inst_13))
                (@RootPairing.rootSpan_ne_bot.{0, 0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
                  inst_9 P S inst_12 inst_13 inst_14 inst_15)
                u)))))
  -- Phase 1: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_1 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_1 : (9 : Nat) = 9 ∨ (9 : Nat) < 9 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 9)
    cases h_dich_1 with
    | inr h_contra_1 => exact False.elim (Nat.lt_irrefl 9 h_contra_1)
    | inl h_refl_1 => exact (And.intro hp h_refl_1).1
  have h_stage_1 := h_ord_1 h_core
  -- Phase 2: Redundant implication-chain mediation
  have h_med_2 : ∀ {P : Prop}, P → (True → P) ∧ (P → P) := fun hp =>
    And.intro (fun _ => id hp) (fun h => (And.intro h hp).1)
  have h_stage_2 := (h_med_2 h_stage_1).2 ((h_med_2 h_stage_1).1 True.intro)
  -- Phase 3: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_3 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_3 : (26 : Nat) = 26 ∨ (26 : Nat) < 26 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 26)
    cases h_dich_3 with
    | inr h_contra_3 => exact False.elim (Nat.lt_irrefl 26 h_contra_3)
    | inl h_refl_3 => exact (And.intro hp h_refl_3).1
  have h_stage_3 := h_ord_3 h_stage_2
  -- Phase 4: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_4 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_4 : (9 + 14 : Nat) = 23 then
      have h_pack_4 := And.intro h_arith_4 hp
      exact h_pack_4.2
    else
      exact False.elim (h_arith_4 rfl)
  have h_stage_4 := h_chk_4 h_stage_3
  -- Phase 5: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_5 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_5 : (5 + 7 : Nat) = 12 then
      have h_pack_5 := And.intro h_arith_5 hp
      exact h_pack_5.2
    else
      exact False.elim (h_arith_5 rfl)
  have h_stage_5 := h_chk_5 h_stage_4
  -- Final step: conclude after 5 auxiliary verification stage(s)
  exact id h_stage_5
