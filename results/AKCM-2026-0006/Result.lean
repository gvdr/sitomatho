import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: WeierstrassCurve.twoTorsionPolynomial_discr (WeierstrassCurve)
-- Step 1: Associated.of_eq (Associated)
-- Step 5: Associated.isUnit (Associated)
-- Step 9: Ring.mul_inverse_cancel_left (Ring)
-- Step 10: Dvd.intro_left (Dvd)
-- Step 11: IsRelPrime.add_one_right_of_dvd (IsRelPrime)
theorem akcm_2026_0006
    {R : Type}
    [inst_2 : CommRing.{0} R]
    (W : WeierstrassCurve.{0} R)
    {u : R}
    (h_5 : @IsUnit.{0} R
  (@Semiring.toMonoid.{0} R
    (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
  (@Cubic.discr.{0} R (@CommRing.toRing.{0} R inst_2)
    (@WeierstrassCurve.twoTorsionPolynomial.{0} R inst_2 W))) :
    @IsRelPrime.{0} R
  (@Semiring.toMonoid.{0} R
    (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
  (@HMul.hMul.{0, 0, 0} R R R
    (@instHMul.{0} R
      (@MulZeroClass.toMul.{0} R
        (@MulZeroOneClass.toMulZeroClass.{0} R
          (@MonoidWithZero.toMulZeroOneClass.{0} R
            (@Semiring.toMonoidWithZero.{0} R
              (@CommSemiring.toSemiring.{0} R
                (@CommRing.toCommSemiring.{0} R inst_2)))))))
    (@Ring.inverse.{0} R
      (@Semiring.toMonoidWithZero.{0} R
        (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
      (@HMul.hMul.{0, 0, 0} R R R
        (@instHMul.{0} R
          (@Distrib.toMul.{0} R
            (@instDistribOfSemiring.{0} R
              (@CommSemiring.toSemiring.{0} R
                (@CommRing.toCommSemiring.{0} R inst_2)))))
        (@OfNat.ofNat.{0} R (nat_lit 16)
          (@instOfNatAtLeastTwo.{0} R (nat_lit 16)
            (@AddMonoidWithOne.toNatCast.{0} R
              (@AddGroupWithOne.toAddMonoidWithOne.{0} R
                (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))
            (@Nat.instAtLeastTwoHAddOfNat
              (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
              (@Nat.instNeZeroSucc
                (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
        (@WeierstrassCurve.Δ.{0} R inst_2 W)))
    u)
  (@HAdd.hAdd.{0, 0, 0} R R R
    (@instHAdd.{0} R
      (@Distrib.toAdd.{0} R
        (@instDistribOfSemiring.{0} R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))
    u
    (@OfNat.ofNat.{0} R (nat_lit 1)
      (@One.toOfNat1.{0} R
        (@AddMonoidWithOne.toOne.{0} R
          (@AddGroupWithOne.toAddMonoidWithOne.{0} R
            (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))))) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @IsRelPrime.add_one_right_of_dvd.{0} R inst_2
      (@HMul.hMul.{0, 0, 0} R R R
        (@instHMul.{0} R
          (@MulZeroClass.toMul.{0} R
            (@MulZeroOneClass.toMulZeroClass.{0} R
              (@MonoidWithZero.toMulZeroOneClass.{0} R
                (@Semiring.toMonoidWithZero.{0} R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))))
        (@Ring.inverse.{0} R
          (@Semiring.toMonoidWithZero.{0} R
            (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
          (@HMul.hMul.{0, 0, 0} R R R
            (@instHMul.{0} R
              (@Distrib.toMul.{0} R
                (@instDistribOfSemiring.{0} R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))
            (@OfNat.ofNat.{0} R (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} R (nat_lit 16)
                (@AddMonoidWithOne.toNatCast.{0} R
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} R
                    (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc
                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
            (@WeierstrassCurve.Δ.{0} R inst_2 W)))
        u)
      u
      (@Dvd.intro_left.{0} R
        (@NonUnitalCommSemiring.toCommSemigroup.{0} R
          (@NonUnitalCommRing.toNonUnitalCommSemiring.{0} R
            (@CommRing.toNonUnitalCommRing.{0} R inst_2)))
        (@HMul.hMul.{0, 0, 0} R R R
          (@instHMul.{0} R
            (@MulZeroClass.toMul.{0} R
              (@MulZeroOneClass.toMulZeroClass.{0} R
                (@MonoidWithZero.toMulZeroOneClass.{0} R
                  (@Semiring.toMonoidWithZero.{0} R
                    (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))))
          (@Ring.inverse.{0} R
            (@Semiring.toMonoidWithZero.{0} R
              (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
            (@HMul.hMul.{0, 0, 0} R R R
              (@instHMul.{0} R
                (@Distrib.toMul.{0} R
                  (@instDistribOfSemiring.{0} R
                    (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))
              (@OfNat.ofNat.{0} R (nat_lit 16)
                (@instOfNatAtLeastTwo.{0} R (nat_lit 16)
                  (@AddMonoidWithOne.toNatCast.{0} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} R
                      (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
              (@WeierstrassCurve.Δ.{0} R inst_2 W)))
          u)
        u
        (@HMul.hMul.{0, 0, 0} R R R
          (@instHMul.{0} R
            (@Distrib.toMul.{0} R
              (@instDistribOfSemiring.{0} R
                (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))
          (@OfNat.ofNat.{0} R (nat_lit 16)
            (@instOfNatAtLeastTwo.{0} R (nat_lit 16)
              (@AddMonoidWithOne.toNatCast.{0} R
                (@AddGroupWithOne.toAddMonoidWithOne.{0} R
                  (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                (@Nat.instNeZeroSucc
                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
          (@WeierstrassCurve.Δ.{0} R inst_2 W))
        (@Ring.mul_inverse_cancel_left.{0} R
          (@Semiring.toMonoidWithZero.{0} R
            (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
          (@HMul.hMul.{0, 0, 0} R R R
            (@instHMul.{0} R
              (@Distrib.toMul.{0} R
                (@instDistribOfSemiring.{0} R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))
            (@OfNat.ofNat.{0} R (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} R (nat_lit 16)
                (@AddMonoidWithOne.toNatCast.{0} R
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} R
                    (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))
                (@Nat.instAtLeastTwoHAddOfNat
                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc
                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
            (@WeierstrassCurve.Δ.{0} R inst_2 W))
          u
          (@Associated.isUnit.{0} R
            (@Semiring.toMonoid.{0} R
              (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
            (@Cubic.discr.{0} R (@CommRing.toRing.{0} R inst_2)
              (@WeierstrassCurve.twoTorsionPolynomial.{0} R inst_2 W))
            (@HMul.hMul.{0, 0, 0} R R R
              (@instHMul.{0} R
                (@Distrib.toMul.{0} R
                  (@instDistribOfSemiring.{0} R
                    (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))
              (@OfNat.ofNat.{0} R (nat_lit 16)
                (@instOfNatAtLeastTwo.{0} R (nat_lit 16)
                  (@AddMonoidWithOne.toNatCast.{0} R
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} R
                      (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
              (@WeierstrassCurve.Δ.{0} R inst_2 W))
            (@Associated.of_eq.{0} R
              (@Semiring.toMonoid.{0} R
                (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
              (@Cubic.discr.{0} R (@CommRing.toRing.{0} R inst_2)
                (@WeierstrassCurve.twoTorsionPolynomial.{0} R inst_2 W))
              (@HMul.hMul.{0, 0, 0} R R R
                (@instHMul.{0} R
                  (@Distrib.toMul.{0} R
                    (@instDistribOfSemiring.{0} R
                      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))))
                (@OfNat.ofNat.{0} R (nat_lit 16)
                  (@instOfNatAtLeastTwo.{0} R (nat_lit 16)
                    (@AddMonoidWithOne.toNatCast.{0} R
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} R
                        (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_2))))
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                (@WeierstrassCurve.Δ.{0} R inst_2 W))
              (@WeierstrassCurve.twoTorsionPolynomial_discr.{0} R inst_2 W))
            h_5)))
  -- Phase 1: Inductive case-analysis ceremony on a trivial index
  have h_lift_1 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_1 := h_lift_1 h_core 0 rfl
  -- Phase 2: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_2 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_2 : (21 : Nat) = 21 ∨ (21 : Nat) < 21 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 21)
    cases h_dich_2 with
    | inr h_contra_2 => exact False.elim (Nat.lt_irrefl 21 h_contra_2)
    | inl h_refl_2 => exact (And.intro hp h_refl_2).1
  have h_stage_2 := h_ord_2 h_stage_1
  -- Final step: conclude after 2 auxiliary verification stage(s)
  exact id h_stage_2
