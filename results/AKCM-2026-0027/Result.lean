import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: MeasureTheory.Measure.join_apply₀ (MeasureTheory)
-- Step 1: Eq.dvd (Eq)
-- Step 2: isUnit_of_dvd_unit (isUnit_of_dvd_unit)
-- Step 6: IsUnit.mul_left_injective (IsUnit)
-- Step 7: Function.Injective.map_count_le (Function)
-- Step 11: LE.le.absolutelyContinuous (LE)
theorem akcm_2026_0027
    {α : Type}
    {mα : MeasurableSpace.{0} α}
    {m : @MeasureTheory.Measure.{0} (@MeasureTheory.Measure.{0} α mα)
  (@MeasureTheory.Measure.instMeasurableSpace.{0} α mα)}
    {s : Set.{0} α}
    (hs : @MeasureTheory.NullMeasurableSet.{0} α mα s (@MeasureTheory.Measure.join.{0} α mα m))
    (h_6 : @IsUnit.{0} ENNReal
  (@CommMonoid.toMonoid.{0} ENNReal
    (@CommSemiring.toCommMonoid.{0} ENNReal ENNReal.instCommSemiring))
  (@MeasureTheory.lintegral.{0} (@MeasureTheory.Measure.{0} α mα)
    (@MeasureTheory.Measure.instMeasurableSpace.{0} α mα) m fun μ ↦
    @DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α)
      (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α mα) μ s))
    (h_7 : @Measurable.{0, 0} ENNReal ENNReal ENNReal.measurableSpace ENNReal.measurableSpace
  fun x ↦
  @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
    (@instHMul.{0} ENNReal
      (@MulOne.toMul.{0} ENNReal
        (@MulOneClass.toMulOne.{0} ENNReal
          (@Monoid.toMulOneClass.{0} ENNReal
            (@CommMonoid.toMonoid.{0} ENNReal
              (@CommSemiring.toCommMonoid.{0} ENNReal ENNReal.instCommSemiring))))))
    x
    (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α)
      (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α mα)
      (@MeasureTheory.Measure.join.{0} α mα m) s)) :
    @MeasureTheory.Measure.AbsolutelyContinuous.{0} ENNReal ENNReal.measurableSpace
  (@MeasureTheory.Measure.map.{0, 0} ENNReal ENNReal ENNReal.measurableSpace
    ENNReal.measurableSpace
    (fun x ↦
      @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@MulOne.toMul.{0} ENNReal
            (@MulOneClass.toMulOne.{0} ENNReal
              (@Monoid.toMulOneClass.{0} ENNReal
                (@CommMonoid.toMonoid.{0} ENNReal
                  (@CommSemiring.toCommMonoid.{0} ENNReal ENNReal.instCommSemiring))))))
        x
        (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α)
          (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α mα)
          (@MeasureTheory.Measure.join.{0} α mα m) s))
    (@MeasureTheory.Measure.count.{0} ENNReal ENNReal.measurableSpace))
  (@MeasureTheory.Measure.count.{0} ENNReal ENNReal.measurableSpace) :=   @LE.le.absolutelyContinuous.{0} ENNReal ENNReal.measurableSpace
  (@MeasureTheory.Measure.map.{0, 0} ENNReal ENNReal ENNReal.measurableSpace
    ENNReal.measurableSpace
    (fun x ↦
      @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@MulOne.toMul.{0} ENNReal
            (@MulOneClass.toMulOne.{0} ENNReal
              (@Monoid.toMulOneClass.{0} ENNReal
                (@CommMonoid.toMonoid.{0} ENNReal
                  (@CommSemiring.toCommMonoid.{0} ENNReal ENNReal.instCommSemiring))))))
        x
        (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α) (fun x ↦ ENNReal)
          (@MeasureTheory.Measure.instFunLike.{0} α mα) (@MeasureTheory.Measure.join.{0} α mα m)
          s))
    (@MeasureTheory.Measure.count.{0} ENNReal ENNReal.measurableSpace))
  (@MeasureTheory.Measure.count.{0} ENNReal ENNReal.measurableSpace)
  (@Function.Injective.map_count_le.{0, 0} ENNReal ENNReal ENNReal.measurableSpace
    ENNReal.measurableSpace
    (fun x ↦
      @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@MulOne.toMul.{0} ENNReal
            (@MulOneClass.toMulOne.{0} ENNReal
              (@Monoid.toMulOneClass.{0} ENNReal
                (@CommMonoid.toMonoid.{0} ENNReal
                  (@CommSemiring.toCommMonoid.{0} ENNReal ENNReal.instCommSemiring))))))
        x
        (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α) (fun x ↦ ENNReal)
          (@MeasureTheory.Measure.instFunLike.{0} α mα) (@MeasureTheory.Measure.join.{0} α mα m)
          s))
    (@IsUnit.mul_left_injective.{0} ENNReal
      (@CommMonoid.toMonoid.{0} ENNReal
        (@CommSemiring.toCommMonoid.{0} ENNReal ENNReal.instCommSemiring))
      (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α) (fun x ↦ ENNReal)
        (@MeasureTheory.Measure.instFunLike.{0} α mα) (@MeasureTheory.Measure.join.{0} α mα m)
        s)
      (@isUnit_of_dvd_unit.{0} ENNReal
        (@CommSemiring.toCommMonoid.{0} ENNReal ENNReal.instCommSemiring)
        (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α) (fun x ↦ ENNReal)
          (@MeasureTheory.Measure.instFunLike.{0} α mα) (@MeasureTheory.Measure.join.{0} α mα m)
          s)
        (@MeasureTheory.lintegral.{0} (@MeasureTheory.Measure.{0} α mα)
          (@MeasureTheory.Measure.instMeasurableSpace.{0} α mα) m fun μ ↦
          @DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α)
            (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α mα) μ s)
        (@Eq.dvd.{0} ENNReal
          (@Semiring.toMonoid.{0} ENNReal
            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
          (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α)
            (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α mα)
            (@MeasureTheory.Measure.join.{0} α mα m) s)
          (@MeasureTheory.lintegral.{0} (@MeasureTheory.Measure.{0} α mα)
            (@MeasureTheory.Measure.instMeasurableSpace.{0} α mα) m fun μ ↦
            @DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α mα) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α mα) μ s)
          (@MeasureTheory.Measure.join_apply₀.{0} α mα m s hs))
        h_6))
    h_7)
