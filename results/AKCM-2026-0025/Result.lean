import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.CauSeq.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: PadicSeq.not_equiv_zero_const_of_ne_zero (PadicSeq)
-- Step 6: PadicSeq.norm_eq_zpow_neg_valuation (PadicSeq)
-- Step 7: dvd_of_eq (dvd_of_eq)
-- Step 8: ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero)
-- Step 9: mul_right_surjective₀ (mul_right_surjective₀)
-- Step 10: IsClosedMap.isQuotientMap (IsClosedMap)
theorem akcm_2026_0025
    {p : Nat}
    [inst_2 : Fact (Nat.Prime p)]
    {q : Rat}
    (hq : @Ne.{1} Rat q (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
    (h_5 : @Ne.{1} Rat
  (@HPow.hPow.{0, 0, 0} Rat Int Rat (@instHPow.{0, 0} Rat Int Rat.instPowInt)
    (@Nat.cast.{0} Rat Rat.instNatCast p)
    (@Neg.neg.{0} Int Int.instNegInt
      (@PadicSeq.valuation p inst_2
        (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
          Rat.instIsStrictOrderedRing
          (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
          (@padicNorm.instIsAbsoluteValueRat p inst_2) q))))
  (@OfNat.ofNat.{0} Rat (nat_lit 0)
    (@Zero.toOfNat0.{0} Rat
      (@MulZeroClass.toZero.{0} Rat
        (@MulZeroOneClass.toMulZeroClass.{0} Rat
          (@MonoidWithZero.toMulZeroOneClass.{0} Rat
            (@Semiring.toMonoidWithZero.{0} Rat Rat.semiring)))))))
    (h_6 : @IsClosedMap.{0, 0} Rat Rat
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
  fun g ↦
  @HMul.hMul.{0, 0, 0} Rat Rat Rat
    (@instHMul.{0} Rat
      (@MulZeroClass.toMul.{0} Rat
        (@MulZeroOneClass.toMulZeroClass.{0} Rat
          (@MonoidWithZero.toMulZeroOneClass.{0} Rat
            (@GroupWithZero.toMonoidWithZero.{0} Rat
              (@DivisionSemiring.toGroupWithZero.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat
                  (@Field.toSemifield.{0} Rat Rat.instField))))))))
    g
    (@PadicSeq.norm p inst_2
      (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
        Rat.instIsStrictOrderedRing
        (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
        (@padicNorm.instIsAbsoluteValueRat p inst_2) q)))
    (h_7 : @Continuous.{0, 0} Rat Rat
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
  fun g ↦
  @HMul.hMul.{0, 0, 0} Rat Rat Rat
    (@instHMul.{0} Rat
      (@MulZeroClass.toMul.{0} Rat
        (@MulZeroOneClass.toMulZeroClass.{0} Rat
          (@MonoidWithZero.toMulZeroOneClass.{0} Rat
            (@GroupWithZero.toMonoidWithZero.{0} Rat
              (@DivisionSemiring.toGroupWithZero.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat
                  (@Field.toSemifield.{0} Rat Rat.instField))))))))
    g
    (@PadicSeq.norm p inst_2
      (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
        Rat.instIsStrictOrderedRing
        (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
        (@padicNorm.instIsAbsoluteValueRat p inst_2) q))) :
    @Topology.IsQuotientMap.{0, 0} Rat Rat
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
  fun g ↦
  @HMul.hMul.{0, 0, 0} Rat Rat Rat
    (@instHMul.{0} Rat
      (@MulZeroClass.toMul.{0} Rat
        (@MulZeroOneClass.toMulZeroClass.{0} Rat
          (@MonoidWithZero.toMulZeroOneClass.{0} Rat
            (@GroupWithZero.toMonoidWithZero.{0} Rat
              (@DivisionSemiring.toGroupWithZero.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat
                  (@Field.toSemifield.{0} Rat Rat.instField))))))))
    g
    (@PadicSeq.norm p inst_2
      (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
        Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
        (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q)) :=   @IsClosedMap.isQuotientMap.{0, 0} Rat Rat
  (fun g ↦
    @HMul.hMul.{0, 0, 0} Rat Rat Rat
      (@instHMul.{0} Rat
        (@MulZeroClass.toMul.{0} Rat
          (@MulZeroOneClass.toMulZeroClass.{0} Rat
            (@MonoidWithZero.toMulZeroOneClass.{0} Rat
              (@GroupWithZero.toMonoidWithZero.{0} Rat
                (@DivisionSemiring.toGroupWithZero.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat
                    (@Field.toSemifield.{0} Rat Rat.instField))))))))
      g
      (@PadicSeq.norm p inst_2
        (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing
          (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
          (@padicNorm.instIsAbsoluteValueRat p inst_2) q)))
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
  h_6 h_7
  (@mul_right_surjective₀.{0} Rat
    (@DivisionSemiring.toGroupWithZero.{0} Rat
      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
    (@PadicSeq.norm p inst_2
      (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing
        (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
        (@padicNorm.instIsAbsoluteValueRat p inst_2) q))
    (@ne_zero_of_dvd_ne_zero.{0} Rat (@Semiring.toMonoidWithZero.{0} Rat Rat.semiring)
      (@PadicSeq.norm p inst_2
        (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing
          (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing) (padicNorm p)
          (@padicNorm.instIsAbsoluteValueRat p inst_2) q))
      (@HPow.hPow.{0, 0, 0} Rat Int Rat (@instHPow.{0, 0} Rat Int Rat.instPowInt)
        (@Nat.cast.{0} Rat Rat.instNatCast p)
        (@Neg.neg.{0} Int Int.instNegInt
          (@PadicSeq.valuation p inst_2
            (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
              Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
              (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q))))
      h_5
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
                Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q))))
        (@PadicSeq.norm_eq_zpow_neg_valuation p inst_2
          (@CauSeq.const.{0, 0} Rat Rat Rat.instField Rat.linearOrder
            Rat.instIsStrictOrderedRing (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
            (padicNorm p) (@padicNorm.instIsAbsoluteValueRat p inst_2) q)
          (@PadicSeq.not_equiv_zero_const_of_ne_zero p inst_2 q hq)))))
