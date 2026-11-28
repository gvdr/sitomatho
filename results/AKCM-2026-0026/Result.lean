import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Notation
import Mathlib.RingTheory.Multiplicity

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: MeasureTheory.measure_union_add_inter₀' (MeasureTheory)
-- Step 1: dvd_of_eq (dvd_of_eq)
-- Step 8: emultiplicity_pos_of_dvd (emultiplicity_pos_of_dvd)
-- Step 9: notMem_botSet_of_lt (notMem_botSet_of_lt)
-- Step 10: Set.disjoint_powerset_insert (Set)
-- Step 11: Disjoint.le_compl_right (Disjoint)
-- Step 12: Set.nonempty_Icc_subtype (Set)
theorem akcm_2026_0026
    {α : Type}
    {m0 : MeasurableSpace.{0} α}
    {μ : @MeasureTheory.Measure.{0} α m0}
    {s : Set.{0} α}
    (hs : @MeasureTheory.NullMeasurableSet.{0} α m0 s μ)
    (t : Set.{0} α) :
    Nonempty.{1}
  (@Set.Elem.{0} (Set.{0} (Set.{0} ENat))
    (@Set.Icc.{0} (Set.{0} (Set.{0} ENat))
      (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} ENat))
        (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} (Set.{0} ENat))
          (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} (Set.{0} ENat))
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} ENat))
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                (Set.{0} (Set.{0} ENat))
                (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} ENat)))))))
      (@Set.powerset.{0} ENat (@botSet.{0} ENat instLinearOrderENat))
      (@compl.{0} (Set.{0} (Set.{0} ENat))
        (@HeytingAlgebra.toCompl.{0} (Set.{0} (Set.{0} ENat))
          (@Order.Frame.toHeytingAlgebra.{0} (Set.{0} (Set.{0} ENat))
            (@CompleteDistribLattice.toFrame.{0} (Set.{0} (Set.{0} ENat))
              (@CompleteBooleanAlgebra.toCompleteDistribLattice.{0}
                (Set.{0} (Set.{0} ENat))
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} (Set.{0} ENat))
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} ENat)))))))
        (@Set.image.{0, 0} (Set.{0} ENat) (Set.{0} ENat)
          (@insert.{0, 0} ENat (Set.{0} ENat) (@Set.instInsert.{0} ENat)
            (@emultiplicity.{0} ENNReal
              (@Semiring.toMonoid.{0} ENNReal
                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
              (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHAdd.{0} ENNReal ENNReal.instAdd)
                (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                  (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
                  (@max.{0} (Set.{0} α) (@Set.instMax.{0} α) s t))
                (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                  (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
                  (@min.{0} (Set.{0} α) (@Set.instMin.{0} α) s t)))
              (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHAdd.{0} ENNReal ENNReal.instAdd)
                (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                  (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ s)
                (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                  (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
                  t))))
          (@Set.powerset.{0} ENat (@botSet.{0} ENat instLinearOrderENat)))))) :=   @Set.nonempty_Icc_subtype.{0} (Set.{0} (Set.{0} ENat))
  (@PartialOrder.toPreorder.{0} (Set.{0} (Set.{0} ENat))
    (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} (Set.{0} ENat))
      (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} (Set.{0} ENat))
        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Set.{0} ENat))
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Set.{0} ENat))
            (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} ENat)))))))
  (@Set.powerset.{0} ENat (@botSet.{0} ENat instLinearOrderENat))
  (@compl.{0} (Set.{0} (Set.{0} ENat))
    (@HeytingAlgebra.toCompl.{0} (Set.{0} (Set.{0} ENat))
      (@Order.Frame.toHeytingAlgebra.{0} (Set.{0} (Set.{0} ENat))
        (@CompleteDistribLattice.toFrame.{0} (Set.{0} (Set.{0} ENat))
          (@CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (Set.{0} (Set.{0} ENat))
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Set.{0} ENat))
              (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} ENat)))))))
    (@Set.image.{0, 0} (Set.{0} ENat) (Set.{0} ENat)
      (@insert.{0, 0} ENat (Set.{0} ENat) (@Set.instInsert.{0} ENat)
        (@emultiplicity.{0} ENNReal
          (@Semiring.toMonoid.{0} ENNReal
            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@max.{0} (Set.{0} α) (@Set.instMax.{0} α) s t))
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@min.{0} (Set.{0} α) (@Set.instMin.{0} α) s t)))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ s)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ t))))
      (@Set.powerset.{0} ENat (@botSet.{0} ENat instLinearOrderENat))))
  (@Disjoint.le_compl_right.{0} (Set.{0} (Set.{0} ENat))
    (@Order.Frame.toHeytingAlgebra.{0} (Set.{0} (Set.{0} ENat))
      (@CompleteDistribLattice.toFrame.{0} (Set.{0} (Set.{0} ENat))
        (@CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (Set.{0} (Set.{0} ENat))
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Set.{0} ENat))
            (@Set.instCompleteAtomicBooleanAlgebra.{0} (Set.{0} ENat))))))
    (@Set.powerset.{0} ENat (@botSet.{0} ENat instLinearOrderENat))
    (@Set.image.{0, 0} (Set.{0} ENat) (Set.{0} ENat)
      (@insert.{0, 0} ENat (Set.{0} ENat) (@Set.instInsert.{0} ENat)
        (@emultiplicity.{0} ENNReal
          (@Semiring.toMonoid.{0} ENNReal
            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@max.{0} (Set.{0} α) (@Set.instMax.{0} α) s t))
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@min.{0} (Set.{0} α) (@Set.instMin.{0} α) s t)))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ s)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ t))))
      (@Set.powerset.{0} ENat (@botSet.{0} ENat instLinearOrderENat)))
    (@Set.disjoint_powerset_insert.{0} ENat (@botSet.{0} ENat instLinearOrderENat)
      (@emultiplicity.{0} ENNReal
        (@Semiring.toMonoid.{0} ENNReal
          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
        (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
          (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
            (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
            (@max.{0} (Set.{0} α) (@Set.instMax.{0} α) s t))
          (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
            (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
            (@min.{0} (Set.{0} α) (@Set.instMin.{0} α) s t)))
        (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
          (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
            (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ s)
          (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
            (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ t)))
      (@notMem_botSet_of_lt.{0} ENat instLinearOrderENat
        (@OfNat.ofNat.{0} ENat (nat_lit 0) (@Zero.toOfNat0.{0} ENat instZeroENat))
        (@emultiplicity.{0} ENNReal
          (@Semiring.toMonoid.{0} ENNReal
            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@max.{0} (Set.{0} α) (@Set.instMax.{0} α) s t))
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@min.{0} (Set.{0} α) (@Set.instMin.{0} α) s t)))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ s)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ t)))
        (@emultiplicity_pos_of_dvd.{0} ENNReal
          (@Semiring.toMonoid.{0} ENNReal
            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@max.{0} (Set.{0} α) (@Set.instMax.{0} α) s t))
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
              (@min.{0} (Set.{0} α) (@Set.instMin.{0} α) s t)))
          (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (@instHAdd.{0} ENNReal ENNReal.instAdd)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ s)
            (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
              (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ t))
          (@dvd_of_eq.{0} ENNReal
            (@Semiring.toMonoid.{0} ENNReal
              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))
            (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHAdd.{0} ENNReal ENNReal.instAdd)
              (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
                (@max.{0} (Set.{0} α) (@Set.instMax.{0} α) s t))
              (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ
                (@min.{0} (Set.{0} α) (@Set.instMin.{0} α) s t)))
            (@HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHAdd.{0} ENNReal ENNReal.instAdd)
              (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ s)
              (@DFunLike.coe.{1, 1, 1} (@MeasureTheory.Measure.{0} α m0) (Set.{0} α)
                (fun x ↦ ENNReal) (@MeasureTheory.Measure.instFunLike.{0} α m0) μ t))
            (@MeasureTheory.measure_union_add_inter₀'.{0} α m0 μ s hs t))))))
