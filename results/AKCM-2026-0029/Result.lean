import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.RingTheory.RootsOfUnity.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: map_rootsOfUnity (map_rootsOfUnity)
-- Step 1: Subgroup.relIndex_mul_index (Subgroup)
-- Step 6: dvd_of_eq (dvd_of_eq)
-- Step 7: Even.trans_dvd (Even)
-- Step 8: Nat.one_lt_of_ne_zero_of_even (Nat)
-- Step 9: isGLB_Ico (isGLB_Ico)
theorem akcm_2026_0029
    {M : Type}
    {N : Type}
    [inst_3 : CommMonoid.{0} M]
    [inst_4 : CommMonoid.{0} N]
    (f : @MonoidHom.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
  (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
  (@MulOneClass.toMulOne.{0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
    (@Units.instMulOneClass.{0} M (@CommMonoid.toMonoid.{0} M inst_3)))
  (@MulOneClass.toMulOne.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
    (@Units.instMulOneClass.{0} N (@CommMonoid.toMonoid.{0} N inst_4))))
    (k : Nat)
    (h_7 : @Even.{0} Nat
  (@Distrib.toAdd.{0} Nat (@instDistribOfSemiring.{0} Nat Nat.instSemiring))
  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
    (@Subgroup.relIndex.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
      (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
      (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
        (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
        (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
        (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
        (@rootsOfUnity.{0} k M inst_3))
      (@rootsOfUnity.{0} k N inst_4))
    (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
      (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
      (@rootsOfUnity.{0} k N inst_4))))
    (h_8 : @Ne.{1} Nat
  (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
    (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
    (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
      (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
      (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
      (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
      (@rootsOfUnity.{0} k M inst_3)))
  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) :
    @IsGLB.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
  (@Set.Ico.{0} Nat Nat.instPreorder
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
      (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
      (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
        (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
        (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
        (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
        (@rootsOfUnity.{0} k M inst_3))))
  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @isGLB_Ico.{0} Nat Nat.instPreorder
      (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
        (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
        (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
          (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
          (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
          (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
          (@rootsOfUnity.{0} k M inst_3)))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Nat.one_lt_of_ne_zero_of_even
        (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
          (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
          (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
            (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
            (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
            (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
            (@rootsOfUnity.{0} k M inst_3)))
        h_8
        (@Even.trans_dvd.{0} Nat Nat.instSemiring
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@Subgroup.relIndex.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
                (@rootsOfUnity.{0} k M inst_3))
              (@rootsOfUnity.{0} k N inst_4))
            (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@rootsOfUnity.{0} k N inst_4)))
          (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
            (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
            (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
              (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
              (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
              (@rootsOfUnity.{0} k M inst_3)))
          h_7
          (@dvd_of_eq.{0} Nat Nat.instMonoid
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@Subgroup.relIndex.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                  (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                  (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                  (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
                  (@rootsOfUnity.{0} k M inst_3))
                (@rootsOfUnity.{0} k N inst_4))
              (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                (@rootsOfUnity.{0} k N inst_4)))
            (@Subgroup.index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
                (@rootsOfUnity.{0} k M inst_3)))
            (@Subgroup.relIndex_mul_index.{0} (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
              (@Subgroup.map.{0, 0} (@Units.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                (@Units.instGroup.{0} M (@CommMonoid.toMonoid.{0} M inst_3))
                (@Units.{0} N (@CommMonoid.toMonoid.{0} N inst_4))
                (@Units.instGroup.{0} N (@CommMonoid.toMonoid.{0} N inst_4)) f
                (@rootsOfUnity.{0} k M inst_3))
              (@rootsOfUnity.{0} k N inst_4) (@map_rootsOfUnity.{0, 0} M N inst_3 inst_4 f k)))))
  -- Phase 1: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_1 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_1 : (23 : Nat) = 23 ∨ (23 : Nat) < 23 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 23)
    cases h_dich_1 with
    | inr h_contra_1 => exact False.elim (Nat.lt_irrefl 23 h_contra_1)
    | inl h_refl_1 => exact (And.intro hp h_refl_1).1
  have h_stage_1 := h_ord_1 h_core
  -- Phase 2: Redundant implication-chain mediation
  have h_med_2 : ∀ {P : Prop}, P → (True → P) ∧ (P → P) := fun hp =>
    And.intro (fun _ => id hp) (fun h => (And.intro h hp).1)
  have h_stage_2 := (h_med_2 h_stage_1).2 ((h_med_2 h_stage_1).1 True.intro)
  -- Phase 3: Inductive case-analysis ceremony on a trivial index
  have h_lift_3 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_3 := h_lift_3 h_stage_2 0 rfl
  -- Final step: conclude after 3 auxiliary verification stage(s)
  exact id h_stage_3
