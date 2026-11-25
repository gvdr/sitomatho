import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.Defs
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.SetNotation

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: IntermediateField.fixedField_le (IntermediateField)
-- Step 1: upperBounds_mono_mem (upperBounds_mono_mem)
-- Step 3: IsLUB.isGreatest (IsLUB)
-- Step 4: IsGreatest.biUnion_Iio_eq (IsGreatest)
-- Step 5: Eq.eventuallyEqSet (Eq)
-- Step 6: Filter.EventuallyEqSet.superset (Filter)
theorem akcm_2026_0009
    {F : Type}
    [inst_2 : Field.{0} F]
    {E : Type}
    [inst_4 : Field.{0} E]
    [inst_5 : @Algebra.{0, 0} F E
  (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
  (@CommSemiring.toSemiring.{0} E
    (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))]
    {H1 : @Subgroup.{0}
  (@AlgEquiv.{0, 0, 0} F E E
    (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
    (@CommSemiring.toSemiring.{0} E
      (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
    (@CommSemiring.toSemiring.{0} E
      (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
    inst_5 inst_5)
  (@AlgEquiv.aut.{0, 0} F E
    (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
    (@CommSemiring.toSemiring.{0} E
      (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
    inst_5)}
    {H2 : @Subgroup.{0}
  (@AlgEquiv.{0, 0, 0} F E E
    (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
    (@CommSemiring.toSemiring.{0} E
      (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
    (@CommSemiring.toSemiring.{0} E
      (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
    inst_5 inst_5)
  (@AlgEquiv.aut.{0, 0} F E
    (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
    (@CommSemiring.toSemiring.{0} E
      (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
    inst_5)}
    (h12 : @LE.le.{0}
  (@Subgroup.{0}
    (@AlgEquiv.{0, 0, 0} F E E
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
      (@CommSemiring.toSemiring.{0} E
        (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
      (@CommSemiring.toSemiring.{0} E
        (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
      inst_5 inst_5)
    (@AlgEquiv.aut.{0, 0} F E
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
      (@CommSemiring.toSemiring.{0} E
        (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
      inst_5))
  (@Preorder.toLE.{0}
    (@Subgroup.{0}
      (@AlgEquiv.{0, 0, 0} F E E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
        inst_5 inst_5)
      (@AlgEquiv.aut.{0, 0} F E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
        inst_5))
    (@PartialOrder.toPreorder.{0}
      (@Subgroup.{0}
        (@AlgEquiv.{0, 0, 0} F E E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
          inst_5 inst_5)
        (@AlgEquiv.aut.{0, 0} F E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
          inst_5))
      (@Subgroup.instPartialOrder.{0}
        (@AlgEquiv.{0, 0, 0} F E E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
          inst_5 inst_5)
        (@AlgEquiv.aut.{0, 0} F E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_2))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_4)))
          inst_5))))
  H1 H2)
    {u : Set.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)}
    (h_10 : @Membership.mem.{0, 0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
  (Set.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
  (@Set.instMembership.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
  (@upperBounds.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
    (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
      (@PartialOrder.toPreorder.{0}
        (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
    u)
  (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H2))
    (h_11 : @IsLUB.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
  (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
    (@PartialOrder.toPreorder.{0}
      (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
      (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
  (@upperBounds.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
    (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
      (@PartialOrder.toPreorder.{0}
        (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
    u)
  (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H1))
    {v : Filter.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)} :
    @Filter.EventuallySubset.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5) v
  (@Set.Iio.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
    (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
      (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
    (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H1))
  (⋃ x,
    ⋃ (_ :
      @Membership.mem.{0, 0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (Set.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
        (@Set.instMembership.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
        (@upperBounds.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
            (@PartialOrder.toPreorder.{0}
              (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
              (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
          u)
        x),
      @Set.Iio.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@PartialOrder.toPreorder.{0}
          (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
        x) :=   @Filter.EventuallyEqSet.superset.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
  (⋃ x,
    ⋃ (_ :
      @Membership.mem.{0, 0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (Set.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
        (@Set.instMembership.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
        (@upperBounds.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
            (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
              (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
          u)
        x),
      @Set.Iio.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
        x)
  (@Set.Iio.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
    (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
      (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
    (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H1))
  v
  (@Eq.eventuallyEqSet.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
    (⋃ x,
      ⋃ (_ :
        @Membership.mem.{0, 0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (Set.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
          (@Set.instMembership.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5))
          (@upperBounds.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
            (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
              (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
                (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
            u)
          x),
        @Set.Iio.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
            (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
          x)
    (@Set.Iio.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
      (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
      (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H1))
    v
    (@IsGreatest.biUnion_Iio_eq.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
      (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
      (@upperBounds.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
            (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
        u)
      (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H1)
      (@IsLUB.isGreatest.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
        (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
        (@upperBounds.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@Preorder.toLE.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
            (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
              (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5)))
          u)
        (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H1) h_11
        (@upperBounds_mono_mem.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
          (@PartialOrder.toPreorder.{0} (@IntermediateField.{0, 0} F E inst_2 inst_4 inst_5)
            (@IntermediateField.instPartialOrder.{0, 0} F E inst_2 inst_4 inst_5))
          u (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H2)
          (@IntermediateField.fixedField.{0, 0} F inst_2 E inst_4 inst_5 H1)
          (@IntermediateField.fixedField_le.{0, 0} F inst_2 E inst_4 inst_5 H1 H2 h12) h_10))))
