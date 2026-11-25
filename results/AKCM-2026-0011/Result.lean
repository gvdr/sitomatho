import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.SuccPred.Limit
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Ordinal.one_lt_of_isSuccLimit (Ordinal)
-- Step 2: Ordinal.isSuccLimit_sub (Ordinal)
-- Step 5: Ordinal.isSuccLimit_mul_left (Ordinal)
-- Step 6: Ordinal.isSuccLimit_add (Ordinal)
-- Step 7: Ordinal.isSuccPrelimit_mul_right (Ordinal)
-- Step 8: Order.IsSuccPrelimit.ordinalPred_eq (Order)
theorem akcm_2026_0011
    {o : Ordinal.{0}}
    (h : @Order.IsSuccLimit.{1} Ordinal.{0}
  (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}) o)
    (h_3 : @Order.IsSuccPrelimit.{1} Ordinal.{0}
  (@Preorder.toLT.{1} Ordinal.{0}
    (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
  o)
    {u : Ordinal.{0}}
    {v : Ordinal.{0}}
    (h_6 : @LT.lt.{1} Ordinal.{0}
  (@Preorder.toLT.{1} Ordinal.{0}
    (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
  (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 0)
    (@Zero.toOfNat0.{1} Ordinal.{0} Ordinal.zero.{0}))
  v)
    {w : Ordinal.{0}} :
    @Eq.{2} Ordinal.{0}
  (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
      (@instHMul.{1} Ordinal.{0}
        (@MulZeroClass.toMul.{1} Ordinal.{0}
          (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
            (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0}
              Ordinal.monoidWithZero.{0}))))
      w
      (@HAdd.hAdd.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
        (@instHAdd.{1} Ordinal.{0} Ordinal.add.{0}) u
        (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
          (@instHMul.{1} Ordinal.{0}
            (@MulZeroClass.toMul.{1} Ordinal.{0}
              (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
                (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0}
                  Ordinal.monoidWithZero.{0}))))
          (@HSub.hSub.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
            (@instHSub.{1} Ordinal.{0} Ordinal.sub.{0}) o
            (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1)
              (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))
          v))).pred
  (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
    (@instHMul.{1} Ordinal.{0}
      (@MulZeroClass.toMul.{1} Ordinal.{0}
        (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
          (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0}
            Ordinal.monoidWithZero.{0}))))
    w
    (@HAdd.hAdd.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
      (@instHAdd.{1} Ordinal.{0} Ordinal.add.{0}) u
      (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
        (@instHMul.{1} Ordinal.{0}
          (@MulZeroClass.toMul.{1} Ordinal.{0}
            (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
              (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0}
                Ordinal.monoidWithZero.{0}))))
        (@HSub.hSub.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
          (@instHSub.{1} Ordinal.{0} Ordinal.sub.{0}) o
          (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1)
            (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))
        v))) :=   @Order.IsSuccPrelimit.ordinalPred_eq.{0}
  (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
    (@instHMul.{1} Ordinal.{0}
      (@MulZeroClass.toMul.{1} Ordinal.{0}
        (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
          (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0} Ordinal.monoidWithZero.{0}))))
    w
    (@HAdd.hAdd.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
      (@instHAdd.{1} Ordinal.{0} Ordinal.add.{0}) u
      (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
        (@instHMul.{1} Ordinal.{0}
          (@MulZeroClass.toMul.{1} Ordinal.{0}
            (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
              (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0} Ordinal.monoidWithZero.{0}))))
        (@HSub.hSub.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
          (@instHSub.{1} Ordinal.{0} Ordinal.sub.{0}) o
          (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1)
            (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))
        v)))
  (@Ordinal.isSuccPrelimit_mul_right.{0} w
    (@HAdd.hAdd.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
      (@instHAdd.{1} Ordinal.{0} Ordinal.add.{0}) u
      (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
        (@instHMul.{1} Ordinal.{0}
          (@MulZeroClass.toMul.{1} Ordinal.{0}
            (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
              (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0} Ordinal.monoidWithZero.{0}))))
        (@HSub.hSub.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
          (@instHSub.{1} Ordinal.{0} Ordinal.sub.{0}) o
          (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1)
            (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))
        v))
    (@Ordinal.isSuccLimit_add.{0} u
      (@HMul.hMul.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
        (@instHMul.{1} Ordinal.{0}
          (@MulZeroClass.toMul.{1} Ordinal.{0}
            (@MulZeroOneClass.toMulZeroClass.{1} Ordinal.{0}
              (@MonoidWithZero.toMulZeroOneClass.{1} Ordinal.{0} Ordinal.monoidWithZero.{0}))))
        (@HSub.hSub.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
          (@instHSub.{1} Ordinal.{0} Ordinal.sub.{0}) o
          (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1)
            (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))
        v)
      (@Ordinal.isSuccLimit_mul_left.{0}
        (@HSub.hSub.{1, 1, 1} Ordinal.{0} Ordinal.{0} Ordinal.{0}
          (@instHSub.{1} Ordinal.{0} Ordinal.sub.{0}) o
          (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1)
            (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))
        v
        (@Ordinal.isSuccLimit_sub.{0} o
          (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1)
            (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0}))
          h_3 (@Ordinal.one_lt_of_isSuccLimit.{0} o h))
        h_6)))
