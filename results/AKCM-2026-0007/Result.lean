import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Commute.sub_left (Commute)
-- Step 1: Commute.symm (Commute)
-- Step 2: Commute.neg_left (Commute)
theorem akcm_2026_0007
    {R : Type}
    [inst_2 : NonUnitalNonAssocRing R]
    {a : R}
    {b : R}
    {c : R}
    (h_6 : Commute a c)
    (h_7 : Commute b c) :
    Commute (-c) (a - b) :=
  @Commute.neg_left.{0} R
  (@Distrib.toMul.{0} R
    (@NonUnitalNonAssocSemiring.toDistrib.{0} R
      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} R inst_2)))
  (@NonUnitalNonAssocRing.toHasDistribNeg.{0} R inst_2) c
  (@HSub.hSub.{0, 0, 0} R R R
    (@instHSub.{0} R
      (@SubNegMonoid.toSub.{0} R
        (@AddGroup.toSubNegMonoid.{0} R
          (@AddCommGroup.toAddGroup.{0} R
            (@NonUnitalNonAssocRing.toAddCommGroup.{0} R inst_2)))))
    a b)
  (@Commute.symm.{0} R
    (@Distrib.toMul.{0} R
      (@NonUnitalNonAssocSemiring.toDistrib.{0} R
        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} R inst_2)))
    (@HSub.hSub.{0, 0, 0} R R R
      (@instHSub.{0} R
        (@SubNegMonoid.toSub.{0} R
          (@AddGroup.toSubNegMonoid.{0} R
            (@AddCommGroup.toAddGroup.{0} R
              (@NonUnitalNonAssocRing.toAddCommGroup.{0} R inst_2)))))
      a b)
    c (@Commute.sub_left.{0} R inst_2 a b c h_6 h_7))
