import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.Index

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: IntermediateField.map_fixingSubgroup_index (IntermediateField)
-- Step 1: Associated.of_eq (Associated)
-- Step 4: Associated.isRelPrime_right (Associated)
-- Step 5: IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal (IsRelPrime)
-- Step 6: exists_eq_mul_right_of_dvd (exists_eq_mul_right_of_dvd)
-- Step 7: Associated.dvd' (Associated)
-- Step 8: gcd_dvd_gcd (gcd_dvd_gcd)
theorem akcm_2026_0011
    {F : Type}
    {E : Type}
    (E' : Type)
    [inst_4 : Field.{0} F]
    [inst_5 : Field.{0} E]
    [inst_6 : Field.{0} E']
    [inst_7 : @Algebra.{0, 0} F E
  (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
  (@CommSemiring.toSemiring.{0} E
    (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))]
    [inst_8 : @Algebra.{0, 0} F E'
  (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
  (@CommSemiring.toSemiring.{0} E'
    (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))]
    [inst_9 : @Algebra.{0, 0} E E'
  (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
  (@CommSemiring.toSemiring.{0} E'
    (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))]
    [inst_10 : @IsScalarTower.{0, 0, 0} F E E'
  (@Algebra.toSMul.{0, 0} F E
    (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
    (@CommSemiring.toSemiring.{0} E
      (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
    inst_7)
  (@Algebra.toSMul.{0, 0} E E'
    (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
    (@CommSemiring.toSemiring.{0} E'
      (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
    inst_9)
  (@Algebra.toSMul.{0, 0} F E'
    (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
    (@CommSemiring.toSemiring.{0} E'
      (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
    inst_8)]
    (L : @IntermediateField.{0, 0} F E inst_4 inst_5 inst_7)
    [inst_12 : @Normal.{0, 0} F E inst_4 inst_5 inst_7]
    [inst_13 : @Normal.{0, 0} F E' inst_4 inst_6 inst_8]
    {u : Nat}
    (h_15 : @IsRelPrime.{0} Nat Nat.instMonoid u
  (@Subgroup.index.{0}
    (@AlgEquiv.{0, 0, 0} F E' E'
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
      (@CommSemiring.toSemiring.{0} E'
        (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
      (@CommSemiring.toSemiring.{0} E'
        (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
      inst_8 inst_8)
    (@AlgEquiv.aut.{0, 0} F E'
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
      (@CommSemiring.toSemiring.{0} E'
        (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
      inst_8)
    (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E' inst_6 inst_8
      (@IntermediateField.map.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7 inst_8
        (@IsScalarTower.toAlgHom.{0, 0, 0} F E E'
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
          (@CommSemiring.toSemiring.{0} E'
            (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
          inst_7 inst_9 inst_8 inst_10)
        L))))
    {v : Nat}
    (h_17 : @Dvd.dvd.{0} Nat
  (@semigroupDvd.{0} Nat
    (@Monoid.toSemigroup.{0} Nat (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)))
  u
  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
    (@instHMul.{0} Nat
      (@MulOne.toMul.{0} Nat
        (@MulOneClass.toMulOne.{0} Nat
          (@Monoid.toMulOneClass.{0} Nat
            (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)))))
    v
    (@Subgroup.index.{0}
      (@AlgEquiv.{0, 0, 0} F E E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        inst_7 inst_7)
      (@AlgEquiv.aut.{0, 0} F E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        inst_7)
      (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))))
    (h_18 : @IsPrimal.{0} Nat
  (@Monoid.toSemigroup.{0} Nat (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)) u) :
    @Dvd.dvd.{0} Nat
  (@semigroupDvd.{0} Nat
    (@SemigroupWithZero.toSemigroup.{0} Nat
      (@MonoidWithZero.toSemigroupWithZero.{0} Nat
        (@CommMonoidWithZero.toMonoidWithZero.{0} Nat Nat.instCommMonoidWithZero))))
  (@gcd.{0} Nat Nat.instCommMonoidWithZero instGCDMonoidNat
    (@Subgroup.index.{0}
      (@AlgEquiv.{0, 0, 0} F E E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        inst_7 inst_7)
      (@AlgEquiv.aut.{0, 0} F E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        inst_7)
      (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))
    u)
  (@gcd.{0} Nat Nat.instCommMonoidWithZero instGCDMonoidNat
    (@Subgroup.index.{0}
      (@AlgEquiv.{0, 0, 0} F E' E'
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E'
          (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
        (@CommSemiring.toSemiring.{0} E'
          (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
        inst_8 inst_8)
      (@AlgEquiv.aut.{0, 0} F E'
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E'
          (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
        inst_8)
      (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E' inst_6 inst_8
        (@IntermediateField.map.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7 inst_8
          (@IsScalarTower.toAlgHom.{0, 0, 0} F E E'
            (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
            (@CommSemiring.toSemiring.{0} E'
              (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
            inst_7 inst_9 inst_8 inst_10)
          L)))
    v) :=   @gcd_dvd_gcd.{0} Nat Nat.instCommMonoidWithZero instGCDMonoidNat
  (@Subgroup.index.{0}
    (@AlgEquiv.{0, 0, 0} F E E
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
      (@CommSemiring.toSemiring.{0} E
        (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
      (@CommSemiring.toSemiring.{0} E
        (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
      inst_7 inst_7)
    (@AlgEquiv.aut.{0, 0} F E
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
      (@CommSemiring.toSemiring.{0} E
        (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
      inst_7)
    (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))
  (@Subgroup.index.{0}
    (@AlgEquiv.{0, 0, 0} F E' E'
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
      (@CommSemiring.toSemiring.{0} E'
        (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
      (@CommSemiring.toSemiring.{0} E'
        (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
      inst_8 inst_8)
    (@AlgEquiv.aut.{0, 0} F E'
      (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
      (@CommSemiring.toSemiring.{0} E'
        (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
      inst_8)
    (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E' inst_6 inst_8
      (@IntermediateField.map.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7 inst_8
        (@IsScalarTower.toAlgHom.{0, 0, 0} F E E'
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
          (@CommSemiring.toSemiring.{0} E'
            (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
          inst_7 inst_9 inst_8 inst_10)
        L)))
  u v
  (@Associated.dvd'.{0} Nat Nat.instMonoid
    (@Subgroup.index.{0}
      (@AlgEquiv.{0, 0, 0} F E' E'
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E'
          (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
        (@CommSemiring.toSemiring.{0} E'
          (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
        inst_8 inst_8)
      (@AlgEquiv.aut.{0, 0} F E'
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E'
          (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
        inst_8)
      (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E' inst_6 inst_8
        (@IntermediateField.map.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7 inst_8
          (@IsScalarTower.toAlgHom.{0, 0, 0} F E E'
            (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
            (@CommSemiring.toSemiring.{0} E'
              (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
            inst_7 inst_9 inst_8 inst_10)
          L)))
    (@Subgroup.index.{0}
      (@AlgEquiv.{0, 0, 0} F E E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        inst_7 inst_7)
      (@AlgEquiv.aut.{0, 0} F E
        (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
        (@CommSemiring.toSemiring.{0} E
          (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
        inst_7)
      (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))
    (@Associated.of_eq.{0} Nat Nat.instMonoid
      (@Subgroup.index.{0}
        (@AlgEquiv.{0, 0, 0} F E' E'
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@CommSemiring.toSemiring.{0} E'
            (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
          (@CommSemiring.toSemiring.{0} E'
            (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
          inst_8 inst_8)
        (@AlgEquiv.aut.{0, 0} F E'
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@CommSemiring.toSemiring.{0} E'
            (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
          inst_8)
        (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E' inst_6 inst_8
          (@IntermediateField.map.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7 inst_8
            (@IsScalarTower.toAlgHom.{0, 0, 0} F E E'
              (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
              (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
              (@CommSemiring.toSemiring.{0} E'
                (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
              inst_7 inst_9 inst_8 inst_10)
            L)))
      (@Subgroup.index.{0}
        (@AlgEquiv.{0, 0, 0} F E E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
          inst_7 inst_7)
        (@AlgEquiv.aut.{0, 0} F E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
          inst_7)
        (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))
      (@IntermediateField.map_fixingSubgroup_index.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7
        inst_8 inst_9 inst_10 L inst_12 inst_13)))
  (@exists_eq_mul_right_of_dvd.{0} Nat
    (@Monoid.toSemigroup.{0} Nat (@CommMonoid.toMonoid.{0} Nat Nat.instCommMonoid)) u v
    (@IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal.{0} Nat Nat.instCommMonoid u v
      (@Subgroup.index.{0}
        (@AlgEquiv.{0, 0, 0} F E E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
          inst_7 inst_7)
        (@AlgEquiv.aut.{0, 0} F E
          (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
          (@CommSemiring.toSemiring.{0} E
            (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
          inst_7)
        (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))
      (@Associated.isRelPrime_right.{0} Nat Nat.instMonoid
        (@Subgroup.index.{0}
          (@AlgEquiv.{0, 0, 0} F E' E'
            (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
            (@CommSemiring.toSemiring.{0} E'
              (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
            (@CommSemiring.toSemiring.{0} E'
              (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
            inst_8 inst_8)
          (@AlgEquiv.aut.{0, 0} F E'
            (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
            (@CommSemiring.toSemiring.{0} E'
              (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
            inst_8)
          (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E' inst_6 inst_8
            (@IntermediateField.map.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7 inst_8
              (@IsScalarTower.toAlgHom.{0, 0, 0} F E E'
                (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
                (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
                (@CommSemiring.toSemiring.{0} E'
                  (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
                inst_7 inst_9 inst_8 inst_10)
              L)))
        (@Subgroup.index.{0}
          (@AlgEquiv.{0, 0, 0} F E E
            (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
            (@CommSemiring.toSemiring.{0} E
              (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
            (@CommSemiring.toSemiring.{0} E
              (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
            inst_7 inst_7)
          (@AlgEquiv.aut.{0, 0} F E
            (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
            (@CommSemiring.toSemiring.{0} E
              (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
            inst_7)
          (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))
        u
        (@Associated.of_eq.{0} Nat Nat.instMonoid
          (@Subgroup.index.{0}
            (@AlgEquiv.{0, 0, 0} F E' E'
              (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
              (@CommSemiring.toSemiring.{0} E'
                (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
              (@CommSemiring.toSemiring.{0} E'
                (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
              inst_8 inst_8)
            (@AlgEquiv.aut.{0, 0} F E'
              (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
              (@CommSemiring.toSemiring.{0} E'
                (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
              inst_8)
            (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E' inst_6 inst_8
              (@IntermediateField.map.{0, 0, 0} F E E' inst_4 inst_5 inst_6 inst_7 inst_8
                (@IsScalarTower.toAlgHom.{0, 0, 0} F E E'
                  (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
                  (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5))
                  (@CommSemiring.toSemiring.{0} E'
                    (@Semifield.toCommSemiring.{0} E' (@Field.toSemifield.{0} E' inst_6)))
                  inst_7 inst_9 inst_8 inst_10)
                L)))
          (@Subgroup.index.{0}
            (@AlgEquiv.{0, 0, 0} F E E
              (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
              (@CommSemiring.toSemiring.{0} E
                (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
              (@CommSemiring.toSemiring.{0} E
                (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
              inst_7 inst_7)
            (@AlgEquiv.aut.{0, 0} F E
              (@Semifield.toCommSemiring.{0} F (@Field.toSemifield.{0} F inst_4))
              (@CommSemiring.toSemiring.{0} E
                (@Semifield.toCommSemiring.{0} E (@Field.toSemifield.{0} E inst_5)))
              inst_7)
            (@IntermediateField.fixingSubgroup.{0, 0} F inst_4 E inst_5 inst_7 L))
          (@IntermediateField.map_fixingSubgroup_index.{0, 0, 0} F E E' inst_4 inst_5 inst_6
            inst_7 inst_8 inst_9 inst_10 L inst_12 inst_13))
        h_15)
      h_17 h_18))
