import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.SetLike.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Order.Lattice

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: IsEllipticSequence.isEllipticNet (IsEllipticSequence)
-- Step 1: IsEllipticNet.isEllipticSequence (IsEllipticNet)
-- Step 2: IsEllipticSequence.neg (IsEllipticSequence)
-- Step 3: IsEllipticNet.atomRel_abs₂ (IsEllipticNet)
-- Step 4: Associated.of_eq (Associated)
-- Step 5: Associated.irreducible (Associated)
-- Step 8: Irreducible.not_isSquare (Irreducible)
theorem akcm_2026_0001
    {R : Type}
    [inst_2 : CommRing.{0} R]
    {W : Int → R}
    (h : @IsEllipticSequence.{0} R inst_2 W)
    (one : @Membership.mem.{0, 0} R
  (@Submonoid.{0} R
    (@MulZeroOneClass.toMulOneClass.{0} R
      (@MonoidWithZero.toMulZeroOneClass.{0} R
        (@Semiring.toMonoidWithZero.{0} R
          (@CommSemiring.toSemiring.{0} R
            (@CommRing.toCommSemiring.{0} R inst_2))))))
  (@SetLike.instMembership.{0, 0}
    (@Submonoid.{0} R
      (@MulZeroOneClass.toMulOneClass.{0} R
        (@MonoidWithZero.toMulZeroOneClass.{0} R
          (@Semiring.toMonoidWithZero.{0} R
            (@CommSemiring.toSemiring.{0} R
              (@CommRing.toCommSemiring.{0} R inst_2))))))
    R
    (@Submonoid.instSetLike.{0} R
      (@MulZeroOneClass.toMulOneClass.{0} R
        (@MonoidWithZero.toMulZeroOneClass.{0} R
          (@Semiring.toMonoidWithZero.{0} R
            (@CommSemiring.toSemiring.{0} R
              (@CommRing.toCommSemiring.{0} R inst_2)))))))
  (@nonZeroDivisors.{0} R
    (@Semiring.toMonoidWithZero.{0} R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
  (W (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
    (two : @Membership.mem.{0, 0} R
  (@Submonoid.{0} R
    (@MulZeroOneClass.toMulOneClass.{0} R
      (@MonoidWithZero.toMulZeroOneClass.{0} R
        (@Semiring.toMonoidWithZero.{0} R
          (@CommSemiring.toSemiring.{0} R
            (@CommRing.toCommSemiring.{0} R inst_2))))))
  (@SetLike.instMembership.{0, 0}
    (@Submonoid.{0} R
      (@MulZeroOneClass.toMulOneClass.{0} R
        (@MonoidWithZero.toMulZeroOneClass.{0} R
          (@Semiring.toMonoidWithZero.{0} R
            (@CommSemiring.toSemiring.{0} R
              (@CommRing.toCommSemiring.{0} R inst_2))))))
    R
    (@Submonoid.instSetLike.{0} R
      (@MulZeroOneClass.toMulOneClass.{0} R
        (@MonoidWithZero.toMulZeroOneClass.{0} R
          (@Semiring.toMonoidWithZero.{0} R
            (@CommSemiring.toSemiring.{0} R
              (@CommRing.toCommSemiring.{0} R inst_2)))))))
  (@nonZeroDivisors.{0} R
    (@Semiring.toMonoidWithZero.{0} R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
  (W (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
    (u : Int)
    (v : Int)
    (w : Int)
    (a : Int)
    (h_11 : @Irreducible.{0} R
  (@Semiring.toMonoid.{0} R
    (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
  (@IsEllipticNet.atomRel.{0} R inst_2 W u
    (@abs.{0} Int instLatticeInt Int.instAddGroup v) w a)) :
    Not
  (@IsSquare.{0} R
    (@MulOne.toMul.{0} R
      (@MulOneClass.toMulOne.{0} R
        (@Monoid.toMulOneClass.{0} R
          (@Semiring.toMonoid.{0} R
            (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))))
    (@IsEllipticNet.atomRel.{0} R inst_2 W u v w a)) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Irreducible.not_isSquare.{0} R
      (@Semiring.toMonoid.{0} R
        (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
      (@IsEllipticNet.atomRel.{0} R inst_2 W u v w a)
      (@Associated.irreducible.{0} R
        (@Semiring.toMonoid.{0} R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
        (@IsEllipticNet.atomRel.{0} R inst_2 W u (@abs.{0} Int instLatticeInt Int.instAddGroup v) w
          a)
        (@IsEllipticNet.atomRel.{0} R inst_2 W u v w a)
        (@Associated.of_eq.{0} R
          (@Semiring.toMonoid.{0} R
            (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
          (@IsEllipticNet.atomRel.{0} R inst_2 W u (@abs.{0} Int instLatticeInt Int.instAddGroup v)
            w a)
          (@IsEllipticNet.atomRel.{0} R inst_2 W u v w a)
          (@IsEllipticNet.atomRel_abs₂.{0} R inst_2 W
            (@IsEllipticSequence.neg.{0} R inst_2 W
              (@IsEllipticNet.isEllipticSequence.{0} R inst_2 W
                (@IsEllipticSequence.isEllipticNet.{0} R inst_2 W h one two))
              one two)
            u v w a))
        h_11)
  -- Phase 1: Inductive case-analysis ceremony on a trivial index
  have h_lift_1 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_1 := h_lift_1 h_core 0 rfl
  -- Phase 2: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_2 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_2 : (5 + 7 : Nat) = 12 then
      have h_pack_2 := And.intro h_arith_2 hp
      exact h_pack_2.2
    else
      exact False.elim (h_arith_2 rfl)
  have h_stage_2 := h_chk_2 h_stage_1
  -- Phase 3: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_3 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_3 : (8 : Nat) = 8 ∨ (8 : Nat) < 8 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 8)
    cases h_dich_3 with
    | inr h_contra_3 => exact False.elim (Nat.lt_irrefl 8 h_contra_3)
    | inl h_refl_3 => exact (And.intro hp h_refl_3).1
  have h_stage_3 := h_ord_3 h_stage_2
  -- Phase 4: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_4 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_4 : (6 + 9 : Nat) = 15 then
      have h_pack_4 := And.intro h_arith_4 hp
      exact h_pack_4.2
    else
      exact False.elim (h_arith_4 rfl)
  have h_stage_4 := h_chk_4 h_stage_3
  -- Phase 5: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_5 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_5 : (6 : Nat) = 6 ∨ (6 : Nat) < 6 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 6)
    cases h_dich_5 with
    | inr h_contra_5 => exact False.elim (Nat.lt_irrefl 6 h_contra_5)
    | inl h_refl_5 => exact (And.intro hp h_refl_5).1
  have h_stage_5 := h_ord_5 h_stage_4
  -- Final step: conclude after 5 auxiliary verification stage(s)
  exact id h_stage_5
