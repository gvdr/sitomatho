import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Commute.list_prod_left (Commute)
-- Step 1: Commute.mul_right (Commute)
-- Step 2: Commute.eq (Commute)
theorem akcm_2026_0001
    {M : Type}
    [inst_2 : Monoid M]
    (l : List M)
    (y : M)
    (h : ∀ x ∈ l, Commute x y) :
    l.prod * (y * y) = y * y * l.prod :=
  @Commute.eq.{0} M (@Semigroup.toMul.{0} M (@Monoid.toSemigroup.{0} M inst_2))
  (@List.prod.{0} M
    (@MulOne.toMul.{0} M (@MulOneClass.toMulOne.{0} M (@Monoid.toMulOneClass.{0} M inst_2)))
    (@MulOne.toOne.{0} M (@MulOneClass.toMulOne.{0} M (@Monoid.toMulOneClass.{0} M inst_2))) l)
  (@HMul.hMul.{0, 0, 0} M M M
    (@instHMul.{0} M (@Semigroup.toMul.{0} M (@Monoid.toSemigroup.{0} M inst_2))) y y)
  (@Commute.mul_right.{0} M (@Monoid.toSemigroup.{0} M inst_2)
    (@List.prod.{0} M
      (@MulOne.toMul.{0} M (@MulOneClass.toMulOne.{0} M (@Monoid.toMulOneClass.{0} M inst_2)))
      (@MulOne.toOne.{0} M (@MulOneClass.toMulOne.{0} M (@Monoid.toMulOneClass.{0} M inst_2)))
      l)
    y y (@Commute.list_prod_left.{0} M inst_2 l y h)
    (@Commute.list_prod_left.{0} M inst_2 l y h))
