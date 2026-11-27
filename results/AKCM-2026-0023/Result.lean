import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.CauSeq.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Order.Filter.Defs
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: PadicSeq.not_equiv_zero_const_of_ne_zero (PadicSeq)
-- Step 2: PadicSeq.norm_eq_zpow_neg_valuation (PadicSeq)
-- Step 3: dvd_of_eq (dvd_of_eq)
-- Step 6: IsCoprime.sub_one_right_of_dvd (IsCoprime)
-- Step 7: IsCoprime.isUnit_of_dvd (IsCoprime)
-- Step 8: IsUnit.mul_left_injective (IsUnit)
-- Step 9: Topology.IsEmbedding.mk' (Topology)
theorem akcm_2026_0023
    {p : Nat}
    [inst_2 : Fact (Nat.Prime p)]
    {q : Rat}
    (hq : @Ne.{1} Rat q (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
    (h_5 : @Dvd.dvd.{0} Rat
  (@semigroupDvd.{0} Rat
    (@SemigroupWithZero.toSemigroup.{0} Rat
      (@NonUnitalSemiring.toSemigroupWithZero.{0} Rat
        (@NonUnitalCommSemiring.toNonUnitalSemiring.{0} Rat
          (@CommSemiring.toNonUnitalCommSemiring.{0} Rat
            (@CommRing.toCommSemiring.{0} Rat Rat.commRing))))))
  (@PadicSeq.norm p inst_2
    (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
      Rat.instIsStrictOrderedRing
      (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
      (@padicNorm.instIsAbsoluteValueRat p inst_2) q))
  (@HSub.hSub.{0, 0, 0} Rat Rat Rat
    (@instHSub.{0} Rat
      (@SubNegMonoid.toSub.{0} Rat
        (@AddGroup.toSubNegMonoid.{0} Rat
          (@AddGroupWithOne.toAddGroup.{0} Rat
            (@Ring.toAddGroupWithOne.{0} Rat
              (@CommRing.toRing.{0} Rat Rat.commRing))))))
    (@HPow.hPow.{0, 0, 0} Rat Int Rat (@instHPow.{0, 0} Rat Int Rat.instPowInt)
      (@Nat.cast.{0} Rat Rat.instNatCast p)
      (@Neg.neg.{0} Int Int.instNegInt
        (@PadicSeq.valuation p inst_2
          (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
            Rat.instIsStrictOrderedRing
            (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
            (@padicNorm.instIsAbsoluteValueRat p inst_2) q))))
    (@OfNat.ofNat.{0} Rat (nat_lit 1)
      (@One.toOfNat1.{0} Rat
        (@AddMonoidWithOne.toOne.{0} Rat
          (@AddGroupWithOne.toAddMonoidWithOne.{0} Rat
            (@Ring.toAddGroupWithOne.{0} Rat
              (@CommRing.toRing.{0} Rat Rat.commRing))))))))
    (h_6 : ∀ (x : Rat),
  @Eq.{1} (Filter.{0} Rat)
    (@Filter.comap.{0, 0} Rat Rat
      (fun x ↦
        @HMul.hMul.{0, 0, 0} Rat Rat Rat
          (@instHMul.{0} Rat
            (@MulOne.toMul.{0} Rat
              (@MulOneClass.toMulOne.{0} Rat
                (@Monoid.toMulOneClass.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@CommSemiring.toSemiring.{0} Rat
                      (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))))))
          x
          (@PadicSeq.norm p inst_2
            (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
              Rat.instIsStrictOrderedRing
              (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
              (@padicNorm.instIsAbsoluteValueRat p inst_2) q)))
      (@nhds.{0} Rat
        (@UniformSpace.toTopologicalSpace.{0} Rat
          (@PseudoMetricSpace.toUniformSpace.{0} Rat
            (@SeminormedRing.toPseudoMetricSpace.{0} Rat
              (@SeminormedCommRing.toSeminormedRing.{0} Rat
                (@NormedCommRing.toSeminormedCommRing.{0} Rat
                  (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField))))))
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat
          (@instHMul.{0} Rat
            (@MulOne.toMul.{0} Rat
              (@MulOneClass.toMulOne.{0} Rat
                (@Monoid.toMulOneClass.{0} Rat
                  (@Semiring.toMonoid.{0} Rat
                    (@CommSemiring.toSemiring.{0} Rat
                      (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))))))
          x
          (@PadicSeq.norm p inst_2
            (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
              Rat.instIsStrictOrderedRing
              (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
              (@padicNorm.instIsAbsoluteValueRat p inst_2) q)))))
    (@nhds.{0} Rat
      (@UniformSpace.toTopologicalSpace.{0} Rat
        (@PseudoMetricSpace.toUniformSpace.{0} Rat
          (@SeminormedRing.toPseudoMetricSpace.{0} Rat
            (@SeminormedCommRing.toSeminormedRing.{0} Rat
              (@NormedCommRing.toSeminormedCommRing.{0} Rat
                (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField))))))
      x)) :
    @Topology.IsEmbedding.{0, 0} Rat Rat
  (@UniformSpace.toTopologicalSpace.{0} Rat
    (@PseudoMetricSpace.toUniformSpace.{0} Rat
      (@SeminormedRing.toPseudoMetricSpace.{0} Rat
        (@SeminormedCommRing.toSeminormedRing.{0} Rat
          (@NormedCommRing.toSeminormedCommRing.{0} Rat
            (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField))))))
  (@UniformSpace.toTopologicalSpace.{0} Rat
    (@PseudoMetricSpace.toUniformSpace.{0} Rat
      (@SeminormedRing.toPseudoMetricSpace.{0} Rat
        (@SeminormedCommRing.toSeminormedRing.{0} Rat
          (@NormedCommRing.toSeminormedCommRing.{0} Rat
            (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField))))))
  fun x ↦
  @HMul.hMul.{0, 0, 0} Rat Rat Rat
    (@instHMul.{0} Rat
      (@MulOne.toMul.{0} Rat
        (@MulOneClass.toMulOne.{0} Rat
          (@Monoid.toMulOneClass.{0} Rat
            (@Semiring.toMonoid.{0} Rat
              (@CommSemiring.toSemiring.{0} Rat
                (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))))))
    x
    (@PadicSeq.norm p inst_2
      (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
        Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
        (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q)) :=   @Topology.IsEmbedding.mk'.{0, 0} Rat Rat
  (@UniformSpace.toTopologicalSpace.{0} Rat
    (@PseudoMetricSpace.toUniformSpace.{0} Rat
      (@SeminormedRing.toPseudoMetricSpace.{0} Rat
        (@SeminormedCommRing.toSeminormedRing.{0} Rat
          (@NormedCommRing.toSeminormedCommRing.{0} Rat
            (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField))))))
  (@UniformSpace.toTopologicalSpace.{0} Rat
    (@PseudoMetricSpace.toUniformSpace.{0} Rat
      (@SeminormedRing.toPseudoMetricSpace.{0} Rat
        (@SeminormedCommRing.toSeminormedRing.{0} Rat
          (@NormedCommRing.toSeminormedCommRing.{0} Rat
            (@NormedField.toNormedCommRing.{0} Rat Rat.instNormedField))))))
  (fun x ↦
    @HMul.hMul.{0, 0, 0} Rat Rat Rat
      (@instHMul.{0} Rat
        (@MulOne.toMul.{0} Rat
          (@MulOneClass.toMulOne.{0} Rat
            (@Monoid.toMulOneClass.{0} Rat
              (@Semiring.toMonoid.{0} Rat
                (@CommSemiring.toSemiring.{0} Rat
                  (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))))))
      x
      (@PadicSeq.norm p inst_2
        (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing
          (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
          (@padicNorm.instIsAbsoluteValueRat p inst_2) q)))
  (@IsUnit.mul_left_injective.{0} Rat
    (@Semiring.toMonoid.{0} Rat
      (@CommSemiring.toSemiring.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)))
    (@PadicSeq.norm p inst_2
      (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing
        (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
        (@padicNorm.instIsAbsoluteValueRat p inst_2) q))
    (@IsCoprime.isUnit_of_dvd.{0} Rat (@CommRing.toCommSemiring.{0} Rat Rat.commRing)
      (@PadicSeq.norm p inst_2
        (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing
          (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
          (@padicNorm.instIsAbsoluteValueRat p inst_2) q))
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat
        (@instHSub.{0} Rat
          (@SubNegMonoid.toSub.{0} Rat
            (@AddGroup.toSubNegMonoid.{0} Rat
              (@AddGroupWithOne.toAddGroup.{0} Rat
                (@Ring.toAddGroupWithOne.{0} Rat (@CommRing.toRing.{0} Rat Rat.commRing))))))
        (@HPow.hPow.{0, 0, 0} Rat Int Rat (@instHPow.{0, 0} Rat Int Rat.instPowInt)
          (@Nat.cast.{0} Rat Rat.instNatCast p)
          (@Neg.neg.{0} Int Int.instNegInt
            (@PadicSeq.valuation p inst_2
              (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
                Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q))))
        (@OfNat.ofNat.{0} Rat (nat_lit 1)
          (@One.toOfNat1.{0} Rat
            (@AddMonoidWithOne.toOne.{0} Rat
              (@AddGroupWithOne.toAddMonoidWithOne.{0} Rat
                (@Ring.toAddGroupWithOne.{0} Rat (@CommRing.toRing.{0} Rat Rat.commRing)))))))
      (@IsCoprime.sub_one_right_of_dvd.{0} Rat Rat.commRing
        (@PadicSeq.norm p inst_2
          (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
            Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
            (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q))
        (@HPow.hPow.{0, 0, 0} Rat Int Rat (@instHPow.{0, 0} Rat Int Rat.instPowInt)
          (@Nat.cast.{0} Rat Rat.instNatCast p)
          (@Neg.neg.{0} Int Int.instNegInt
            (@PadicSeq.valuation p inst_2
              (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
                Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q))))
        (@dvd_of_eq.{0} Rat Rat.monoid
          (@PadicSeq.norm p inst_2
            (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
              Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
              (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q))
          (@HPow.hPow.{0, 0, 0} Rat Int Rat (@instHPow.{0, 0} Rat Int Rat.instPowInt)
            (@Nat.cast.{0} Rat Rat.instNatCast p)
            (@Neg.neg.{0} Int Int.instNegInt
              (@PadicSeq.valuation p inst_2
                (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
                  Rat.instIsStrictOrderedRing
                  (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
                  (@padicNorm.instIsAbsoluteValueRat p inst_2) q))))
          (@PadicSeq.norm_eq_zpow_neg_valuation p inst_2
            (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
              Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
              (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q)
            (@PadicSeq.not_equiv_zero_const_of_ne_zero p inst_2 q hq))))
      h_5))
  h_6
