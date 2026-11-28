import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: IsPrimitiveRoot.card_primitiveRoots (IsPrimitiveRoot)
-- Step 1: Associated.of_eq (Associated)
-- Step 9: Associated.symm (Associated)
-- Step 10: lcm_eq_of_associated_left (lcm_eq_of_associated_left)
-- Step 11: Eq.rightDvd (Eq)
-- Step 12: RightDvd.mul_left (RightDvd)
theorem akcm_2026_0031
    {R : Type}
    [inst_2 : CommRing.{0} R]
    [inst_3 : @IsDomain.{0} R
  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))]
    {ζ : R}
    {k : Nat}
    (h : @IsPrimitiveRoot.{0} R (@CommRing.toCommMonoid.{0} R inst_2) ζ k)
    {u : Nat} :
    @RightDvd.{0} Nat (@Monoid.toSemigroup.{0} Nat Nat.instMonoid)
  (@lcm.{0} Nat Nat.instCommMonoidWithZero
    (@NormalizedGCDMonoid.toGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
      (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat
        Nat.instCommMonoidWithZero instStrongNormalizedGCDMonoidNat))
    k.totient k)
  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
    (@instHMul.{0} Nat
      (@Semigroup.toMul.{0} Nat (@Monoid.toSemigroup.{0} Nat Nat.instMonoid)))
    u
    (@lcm.{0} Nat Nat.instCommMonoidWithZero
      (@NormalizedGCDMonoid.toGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
        (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat
          Nat.instCommMonoidWithZero instStrongNormalizedGCDMonoidNat))
      (@Finset.card.{0} R (@primitiveRoots.{0} k R inst_2 inst_3)) k)) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @RightDvd.mul_left.{0} Nat (@Monoid.toSemigroup.{0} Nat Nat.instMonoid)
      (@lcm.{0} Nat Nat.instCommMonoidWithZero
        (@NormalizedGCDMonoid.toGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
          (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
            instStrongNormalizedGCDMonoidNat))
        k.totient k)
      (@lcm.{0} Nat Nat.instCommMonoidWithZero
        (@NormalizedGCDMonoid.toGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
          (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
            instStrongNormalizedGCDMonoidNat))
        (@Finset.card.{0} R (@primitiveRoots.{0} k R inst_2 inst_3)) k)
      (@Eq.rightDvd.{0} Nat Nat.instMonoid
        (@lcm.{0} Nat Nat.instCommMonoidWithZero
          (@NormalizedGCDMonoid.toGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
            (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
              instStrongNormalizedGCDMonoidNat))
          k.totient k)
        (@lcm.{0} Nat Nat.instCommMonoidWithZero
          (@NormalizedGCDMonoid.toGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
            (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
              instStrongNormalizedGCDMonoidNat))
          (@Finset.card.{0} R (@primitiveRoots.{0} k R inst_2 inst_3)) k)
        (@lcm_eq_of_associated_left.{0} Nat Nat.instCommMonoidWithZero
          (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
            instStrongNormalizedGCDMonoidNat)
          k.totient (@Finset.card.{0} R (@primitiveRoots.{0} k R inst_2 inst_3))
          (@Associated.symm.{0} Nat Nat.instMonoid
            (@Finset.card.{0} R (@primitiveRoots.{0} k R inst_2 inst_3)) k.totient
            (@Associated.of_eq.{0} Nat Nat.instMonoid
              (@Finset.card.{0} R (@primitiveRoots.{0} k R inst_2 inst_3)) k.totient
              (@IsPrimitiveRoot.card_primitiveRoots.{0} R inst_2 inst_3 ζ k h)))
          k))
      u
  -- Phase 1: Symmetric conjunction–disjunction transport
  have h_sym_1 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_1 := h_sym_1 h_core
  -- Phase 2: Inductive case-analysis ceremony on a trivial index
  have h_lift_2 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_2 := h_lift_2 h_stage_1 0 rfl
  -- Phase 3: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_3 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_3 : (21 : Nat) = 21 ∨ (21 : Nat) < 21 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 21)
    cases h_dich_3 with
    | inr h_contra_3 => exact False.elim (Nat.lt_irrefl 21 h_contra_3)
    | inl h_refl_3 => exact (And.intro hp h_refl_3).1
  have h_stage_3 := h_ord_3 h_stage_2
  -- Final step: conclude after 3 auxiliary verification stage(s)
  exact id h_stage_3
