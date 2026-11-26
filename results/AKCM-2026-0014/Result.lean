import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Defs
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Representation.Coinvariants.mem_ker_of_eq (Representation)
-- Step 1: zsmul_mem (zsmul_mem)
-- Step 2: vadd_coe_set (vadd_coe_set)
-- Step 3: Eq.superset (Eq)
-- Step 4: mem_of_le_of_mem (mem_of_le_of_mem)
-- Step 5: Set.encard_exchange (Set)
-- Step 6: dvd_of_eq (dvd_of_eq)
-- Step 7: exists_eq_mul_right_of_dvd (exists_eq_mul_right_of_dvd)
-- Step 8: IsCoprime.isUnit_of_dvd' (IsCoprime)
-- Step 9: IsUnit.mul_left_injective (IsUnit)
theorem akcm_2026_0014
    {k : Type}
    {G : Type}
    {V : Type}
    [inst_4 : CommRing.{0} k]
    [inst_5 : Monoid.{0} G]
    [inst_6 : AddCommGroup.{0} V]
    [inst_7 : @Module.{0, 0} k V
  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
  (@AddCommGroup.toAddCommMonoid.{0} V inst_6)]
    {ρ : @Representation.{0, 0, 0} k G V
  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4)) inst_5
  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7}
    (g : G)
    (x : V)
    (a : V)
    (h : @Eq.{1} V
  (@HSub.hSub.{0, 0, 0} V V V
    (@instHSub.{0} V
      (@SubNegMonoid.toSub.{0} V
        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6))))
    (@DFunLike.coe.{1, 1, 1}
      (@LinearMap.{0, 0, 0, 0} k k
        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
        (@RingHom.id.{0} k
          (@Semiring.toNonAssocSemiring.{0} k
            (@CommSemiring.toSemiring.{0} k
              (@CommRing.toCommSemiring.{0} k inst_4))))
        V V (@AddCommGroup.toAddCommMonoid.{0} V inst_6)
        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7 inst_7)
      V (fun x ↦ V)
      (@LinearMap.instFunLike.{0, 0, 0, 0} k k V V
        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
        (@AddCommGroup.toAddCommMonoid.{0} V inst_6)
        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7 inst_7
        (@RingHom.id.{0} k
          (@Semiring.toNonAssocSemiring.{0} k
            (@CommSemiring.toSemiring.{0} k
              (@CommRing.toCommSemiring.{0} k inst_4)))))
      (@DFunLike.coe.{1, 1, 1}
        (@Representation.{0, 0, 0} k G V
          (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
          inst_5 (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
        G
        (fun x ↦
          @LinearMap.{0, 0, 0, 0} k k
            (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
            (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
            (@RingHom.id.{0} k
              (@Semiring.toNonAssocSemiring.{0} k
                (@CommSemiring.toSemiring.{0} k
                  (@CommRing.toCommSemiring.{0} k inst_4))))
            V V (@AddCommGroup.toAddCommMonoid.{0} V inst_6)
            (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7 inst_7)
        (@MonoidHom.instFunLike.{0, 0} G
          (@LinearMap.{0, 0, 0, 0} k k
            (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
            (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
            (@RingHom.id.{0} k
              (@Semiring.toNonAssocSemiring.{0} k
                (@CommSemiring.toSemiring.{0} k
                  (@CommRing.toCommSemiring.{0} k inst_4))))
            V V (@AddCommGroup.toAddCommMonoid.{0} V inst_6)
            (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7 inst_7)
          (@MulOneClass.toMulOne.{0} G (@Monoid.toMulOneClass.{0} G inst_5))
          (@MulOneClass.toMulOne.{0}
            (@LinearMap.{0, 0, 0, 0} k k
              (@CommSemiring.toSemiring.{0} k
                (@CommRing.toCommSemiring.{0} k inst_4))
              (@CommSemiring.toSemiring.{0} k
                (@CommRing.toCommSemiring.{0} k inst_4))
              (@RingHom.id.{0} k
                (@Semiring.toNonAssocSemiring.{0} k
                  (@CommSemiring.toSemiring.{0} k
                    (@CommRing.toCommSemiring.{0} k inst_4))))
              V V (@AddCommGroup.toAddCommMonoid.{0} V inst_6)
              (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7 inst_7)
            (@MulZeroOneClass.toMulOneClass.{0}
              (@LinearMap.{0, 0, 0, 0} k k
                (@CommSemiring.toSemiring.{0} k
                  (@CommRing.toCommSemiring.{0} k inst_4))
                (@CommSemiring.toSemiring.{0} k
                  (@CommRing.toCommSemiring.{0} k inst_4))
                (@RingHom.id.{0} k
                  (@Semiring.toNonAssocSemiring.{0} k
                    (@CommSemiring.toSemiring.{0} k
                      (@CommRing.toCommSemiring.{0} k inst_4))))
                V V (@AddCommGroup.toAddCommMonoid.{0} V inst_6)
                (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7 inst_7)
              (@instMulZeroOneClassOfSemiring.{0}
                (@LinearMap.{0, 0, 0, 0} k k
                  (@CommSemiring.toSemiring.{0} k
                    (@CommRing.toCommSemiring.{0} k inst_4))
                  (@CommSemiring.toSemiring.{0} k
                    (@CommRing.toCommSemiring.{0} k inst_4))
                  (@RingHom.id.{0} k
                    (@Semiring.toNonAssocSemiring.{0} k
                      (@CommSemiring.toSemiring.{0} k
                        (@CommRing.toCommSemiring.{0} k inst_4))))
                  V V (@AddCommGroup.toAddCommMonoid.{0} V inst_6)
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7 inst_7)
                (@Module.End.instSemiring.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k
                    (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)))))
        ρ g)
      x)
    x)
  a)
    (u : Int)
    {v : V}
    (h_15 : v ∉
  @HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
    (@instHVAdd.{0, 0} V (Set.{0} V)
      (@Set.vaddSet.{0, 0} V V
        (@instVAddOfAdd.{0} V
          (@AddZero.toAdd.{0} V
            (@AddZeroClass.toAddZero.{0} V
              (@AddMonoid.toAddZeroClass.{0} V
                (@SubNegMonoid.toAddMonoid.{0} V
                  (@AddGroup.toSubNegMonoid.{0} V
                    (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
    a
    (@SetLike.coe.{0, 0}
      (@Submodule.{0, 0} k V
        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
      V
      (@Submodule.setLike.{0, 0} k V
        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
      (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
        ρ)))
    (h_16 : @IsCoprime.{0} ENat instCommSemiringENat
  (@Set.encard.{0} V
    (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
      (@instHVAdd.{0, 0} V (Set.{0} V)
        (@Set.vaddSet.{0, 0} V V
          (@instVAddOfAdd.{0} V
            (@AddZero.toAdd.{0} V
              (@AddZeroClass.toAddZero.{0} V
                (@AddMonoid.toAddZeroClass.{0} V
                  (@SubNegMonoid.toAddMonoid.{0} V
                    (@AddGroup.toSubNegMonoid.{0} V
                      (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
      a
      (@SetLike.coe.{0, 0}
        (@Submodule.{0, 0} k V
          (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
        V
        (@Submodule.setLike.{0, 0} k V
          (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
        (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6
          inst_7 ρ))))
  (@Set.encard.{0} V
    (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
      (@instHVAdd.{0, 0} V (Set.{0} V)
        (@Set.vaddSet.{0, 0} V V
          (@instVAddOfAdd.{0} V
            (@AddZero.toAdd.{0} V
              (@AddZeroClass.toAddZero.{0} V
                (@AddMonoid.toAddZeroClass.{0} V
                  (@SubNegMonoid.toAddMonoid.{0} V
                    (@AddGroup.toSubNegMonoid.{0} V
                      (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
      a
      (@SetLike.coe.{0, 0}
        (@Submodule.{0, 0} k V
          (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
        V
        (@Submodule.setLike.{0, 0} k V
          (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
        (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6
          inst_7 ρ))))) :
    @Function.Injective.{1, 1} ENat ENat fun x ↦
  @HMul.hMul.{0, 0, 0} ENat ENat ENat
    (@instHMul.{0} ENat
      (@MulOne.toMul.{0} ENat
        (@MulOneClass.toMulOne.{0} ENat
          (@Monoid.toMulOneClass.{0} ENat
            (@Semiring.toMonoid.{0} ENat
              (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))))))
    x
    (@Set.encard.{0} V
      (@insert.{0, 0} V (Set.{0} V) (@Set.instInsert.{0} V) v
        (@sdiff.{0} (Set.{0} V) (@Set.instSDiff.{0} V)
          (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
            (@instHVAdd.{0, 0} V (Set.{0} V)
              (@Set.vaddSet.{0, 0} V V
                (@instVAddOfAdd.{0} V
                  (@AddZero.toAdd.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V
                            (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
            a
            (@SetLike.coe.{0, 0}
              (@Submodule.{0, 0} k V
                (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
              V
              (@Submodule.setLike.{0, 0} k V
                (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
              (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6
                inst_7 ρ)))
          (@singleton.{0, 0} V (Set.{0} V) (@Set.instSingletonSet.{0} V)
            (@HSMul.hSMul.{0, 0, 0} Int V V
              (@instHSMul.{0, 0} Int V
                (@ZSMul.toSMul.{0} V
                  (@SubNegMonoid.toZSMul.{0} V
                    (@AddGroup.toSubNegMonoid.{0} V
                      (@AddCommGroup.toAddGroup.{0} V inst_6)))))
              u a))))) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @IsUnit.mul_left_injective.{0} ENat
      (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
      (@Set.encard.{0} V
        (@insert.{0, 0} V (Set.{0} V) (@Set.instInsert.{0} V) v
          (@sdiff.{0} (Set.{0} V) (@Set.instSDiff.{0} V)
            (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
              (@instHVAdd.{0, 0} V (Set.{0} V)
                (@Set.vaddSet.{0, 0} V V
                  (@instVAddOfAdd.{0} V
                    (@AddZero.toAdd.{0} V
                      (@AddZeroClass.toAddZero.{0} V
                        (@AddMonoid.toAddZeroClass.{0} V
                          (@SubNegMonoid.toAddMonoid.{0} V
                            (@AddGroup.toSubNegMonoid.{0} V
                              (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
              a
              (@SetLike.coe.{0, 0}
                (@Submodule.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                V
                (@Submodule.setLike.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ)))
            (@singleton.{0, 0} V (Set.{0} V) (@Set.instSingletonSet.{0} V)
              (@HSMul.hSMul.{0, 0, 0} Int V V
                (@instHSMul.{0, 0} Int V
                  (@ZSMul.toSMul.{0} V
                    (@SubNegMonoid.toZSMul.{0} V
                      (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                u a)))))
      (@IsCoprime.isUnit_of_dvd'.{0} ENat instCommSemiringENat
        (@Set.encard.{0} V
          (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
            (@instHVAdd.{0, 0} V (Set.{0} V)
              (@Set.vaddSet.{0, 0} V V
                (@instVAddOfAdd.{0} V
                  (@AddZero.toAdd.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V
                            (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
            a
            (@SetLike.coe.{0, 0}
              (@Submodule.{0, 0} k V
                (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
              V
              (@Submodule.setLike.{0, 0} k V
                (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
              (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ))))
        (@Set.encard.{0} V
          (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
            (@instHVAdd.{0, 0} V (Set.{0} V)
              (@Set.vaddSet.{0, 0} V V
                (@instVAddOfAdd.{0} V
                  (@AddZero.toAdd.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V
                            (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
            a
            (@SetLike.coe.{0, 0}
              (@Submodule.{0, 0} k V
                (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
              V
              (@Submodule.setLike.{0, 0} k V
                (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
              (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ))))
        (@Set.encard.{0} V
          (@insert.{0, 0} V (Set.{0} V) (@Set.instInsert.{0} V) v
            (@sdiff.{0} (Set.{0} V) (@Set.instSDiff.{0} V)
              (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                (@instHVAdd.{0, 0} V (Set.{0} V)
                  (@Set.vaddSet.{0, 0} V V
                    (@instVAddOfAdd.{0} V
                      (@AddZero.toAdd.{0} V
                        (@AddZeroClass.toAddZero.{0} V
                          (@AddMonoid.toAddZeroClass.{0} V
                            (@SubNegMonoid.toAddMonoid.{0} V
                              (@AddGroup.toSubNegMonoid.{0} V
                                (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                a
                (@SetLike.coe.{0, 0}
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  V
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ)))
              (@singleton.{0, 0} V (Set.{0} V) (@Set.instSingletonSet.{0} V)
                (@HSMul.hSMul.{0, 0, 0} Int V V
                  (@instHSMul.{0, 0} Int V
                    (@ZSMul.toSMul.{0} V
                      (@SubNegMonoid.toZSMul.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                  u a)))))
        h_16
        (@dvd_of_eq.{0} ENat
          (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
          (@Set.encard.{0} V
            (@insert.{0, 0} V (Set.{0} V) (@Set.instInsert.{0} V) v
              (@sdiff.{0} (Set.{0} V) (@Set.instSDiff.{0} V)
                (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                  (@instHVAdd.{0, 0} V (Set.{0} V)
                    (@Set.vaddSet.{0, 0} V V
                      (@instVAddOfAdd.{0} V
                        (@AddZero.toAdd.{0} V
                          (@AddZeroClass.toAddZero.{0} V
                            (@AddMonoid.toAddZeroClass.{0} V
                              (@SubNegMonoid.toAddMonoid.{0} V
                                (@AddGroup.toSubNegMonoid.{0} V
                                  (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                  a
                  (@SetLike.coe.{0, 0}
                    (@Submodule.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    V
                    (@Submodule.setLike.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                      ρ)))
                (@singleton.{0, 0} V (Set.{0} V) (@Set.instSingletonSet.{0} V)
                  (@HSMul.hSMul.{0, 0, 0} Int V V
                    (@instHSMul.{0, 0} Int V
                      (@ZSMul.toSMul.{0} V
                        (@SubNegMonoid.toZSMul.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V
                            (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                    u a)))))
          (@Set.encard.{0} V
            (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
              (@instHVAdd.{0, 0} V (Set.{0} V)
                (@Set.vaddSet.{0, 0} V V
                  (@instVAddOfAdd.{0} V
                    (@AddZero.toAdd.{0} V
                      (@AddZeroClass.toAddZero.{0} V
                        (@AddMonoid.toAddZeroClass.{0} V
                          (@SubNegMonoid.toAddMonoid.{0} V
                            (@AddGroup.toSubNegMonoid.{0} V
                              (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
              a
              (@SetLike.coe.{0, 0}
                (@Submodule.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                V
                (@Submodule.setLike.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ))))
          (@Set.encard_exchange.{0} V
            (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
              (@instHVAdd.{0, 0} V (Set.{0} V)
                (@Set.vaddSet.{0, 0} V V
                  (@instVAddOfAdd.{0} V
                    (@AddZero.toAdd.{0} V
                      (@AddZeroClass.toAddZero.{0} V
                        (@AddMonoid.toAddZeroClass.{0} V
                          (@SubNegMonoid.toAddMonoid.{0} V
                            (@AddGroup.toSubNegMonoid.{0} V
                              (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
              a
              (@SetLike.coe.{0, 0}
                (@Submodule.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                V
                (@Submodule.setLike.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ)))
            v
            (@HSMul.hSMul.{0, 0, 0} Int V V
              (@instHSMul.{0, 0} Int V
                (@ZSMul.toSMul.{0} V
                  (@SubNegMonoid.toZSMul.{0} V
                    (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6)))))
              u a)
            h_15
            (@mem_of_le_of_mem.{0, 0} (Set.{0} V) V (@Set.instMembership.{0} V)
              (@Preorder.toLE.{0} (Set.{0} V)
                (@PartialOrder.toPreorder.{0} (Set.{0} V)
                  (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} V)
                    (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} V)
                      (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} V)
                        (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} V)
                          (@Set.instCompleteAtomicBooleanAlgebra.{0} V)))))))
              (instIsConcreteLESet.{0} V)
              (@SetLike.coe.{0, 0}
                (@Submodule.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                V
                (@Submodule.setLike.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ))
              (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                (@instHVAdd.{0, 0} V (Set.{0} V)
                  (@Set.vaddSet.{0, 0} V V
                    (@instVAddOfAdd.{0} V
                      (@AddZero.toAdd.{0} V
                        (@AddZeroClass.toAddZero.{0} V
                          (@AddMonoid.toAddZeroClass.{0} V
                            (@SubNegMonoid.toAddMonoid.{0} V
                              (@AddGroup.toSubNegMonoid.{0} V
                                (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                a
                (@SetLike.coe.{0, 0}
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  V
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ)))
              (@Eq.superset.{0} (Set.{0} V) (Set.instUsesSetNotationForOrder.{0} V)
                (@PartialOrder.toPreorder.{0} (Set.{0} V)
                  (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} V)
                    (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} V)
                      (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} V)
                        (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} V)
                          (@Set.instCompleteAtomicBooleanAlgebra.{0} V))))))
                (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                  (@instHVAdd.{0, 0} V (Set.{0} V)
                    (@Set.vaddSet.{0, 0} V V
                      (@instVAddOfAdd.{0} V
                        (@AddZero.toAdd.{0} V
                          (@AddZeroClass.toAddZero.{0} V
                            (@AddMonoid.toAddZeroClass.{0} V
                              (@SubNegMonoid.toAddMonoid.{0} V
                                (@AddGroup.toSubNegMonoid.{0} V
                                  (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                  a
                  (@SetLike.coe.{0, 0}
                    (@Submodule.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    V
                    (@Submodule.setLike.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                      ρ)))
                (@SetLike.coe.{0, 0}
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  V
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ))
                (@vadd_coe_set.{0, 0} V
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@AddCommGroup.toAddGroup.{0} V inst_6)
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Submodule.addSubgroupClass.{0, 0} k V (@CommRing.toRing.{0} k inst_4) inst_6
                    inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ) a
                  (@Representation.Coinvariants.mem_ker_of_eq.{0, 0, 0} k G V inst_4 inst_5 inst_6
                    inst_7 ρ g x a h)))
              (@HSMul.hSMul.{0, 0, 0} Int V V
                (@instHSMul.{0, 0} Int V
                  (@ZSMul.toSMul.{0} V
                    (@SubNegMonoid.toZSMul.{0} V
                      (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                u a)
              (@zsmul_mem.{0, 0} V
                (@Submodule.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6))
                (@Submodule.setLike.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                (@Submodule.addSubgroupClass.{0, 0} k V (@CommRing.toRing.{0} k inst_4) inst_6
                  inst_7)
                (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ) a
                (@Representation.Coinvariants.mem_ker_of_eq.{0, 0, 0} k G V inst_4 inst_5 inst_6
                  inst_7 ρ g x a h)
                u))))
        (@exists_eq_mul_right_of_dvd.{0} ENat
          (@Monoid.toSemigroup.{0} ENat
            (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)))
          (@Set.encard.{0} V
            (@insert.{0, 0} V (Set.{0} V) (@Set.instInsert.{0} V) v
              (@sdiff.{0} (Set.{0} V) (@Set.instSDiff.{0} V)
                (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                  (@instHVAdd.{0, 0} V (Set.{0} V)
                    (@Set.vaddSet.{0, 0} V V
                      (@instVAddOfAdd.{0} V
                        (@AddZero.toAdd.{0} V
                          (@AddZeroClass.toAddZero.{0} V
                            (@AddMonoid.toAddZeroClass.{0} V
                              (@SubNegMonoid.toAddMonoid.{0} V
                                (@AddGroup.toSubNegMonoid.{0} V
                                  (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                  a
                  (@SetLike.coe.{0, 0}
                    (@Submodule.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    V
                    (@Submodule.setLike.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                      ρ)))
                (@singleton.{0, 0} V (Set.{0} V) (@Set.instSingletonSet.{0} V)
                  (@HSMul.hSMul.{0, 0, 0} Int V V
                    (@instHSMul.{0, 0} Int V
                      (@ZSMul.toSMul.{0} V
                        (@SubNegMonoid.toZSMul.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V
                            (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                    u a)))))
          (@Set.encard.{0} V
            (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
              (@instHVAdd.{0, 0} V (Set.{0} V)
                (@Set.vaddSet.{0, 0} V V
                  (@instVAddOfAdd.{0} V
                    (@AddZero.toAdd.{0} V
                      (@AddZeroClass.toAddZero.{0} V
                        (@AddMonoid.toAddZeroClass.{0} V
                          (@SubNegMonoid.toAddMonoid.{0} V
                            (@AddGroup.toSubNegMonoid.{0} V
                              (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
              a
              (@SetLike.coe.{0, 0}
                (@Submodule.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                V
                (@Submodule.setLike.{0, 0} k V
                  (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                  (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ))))
          (@dvd_of_eq.{0} ENat
            (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
            (@Set.encard.{0} V
              (@insert.{0, 0} V (Set.{0} V) (@Set.instInsert.{0} V) v
                (@sdiff.{0} (Set.{0} V) (@Set.instSDiff.{0} V)
                  (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                    (@instHVAdd.{0, 0} V (Set.{0} V)
                      (@Set.vaddSet.{0, 0} V V
                        (@instVAddOfAdd.{0} V
                          (@AddZero.toAdd.{0} V
                            (@AddZeroClass.toAddZero.{0} V
                              (@AddMonoid.toAddZeroClass.{0} V
                                (@SubNegMonoid.toAddMonoid.{0} V
                                  (@AddGroup.toSubNegMonoid.{0} V
                                    (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                    a
                    (@SetLike.coe.{0, 0}
                      (@Submodule.{0, 0} k V
                        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                      V
                      (@Submodule.setLike.{0, 0} k V
                        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                      (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                        ρ)))
                  (@singleton.{0, 0} V (Set.{0} V) (@Set.instSingletonSet.{0} V)
                    (@HSMul.hSMul.{0, 0, 0} Int V V
                      (@instHSMul.{0, 0} Int V
                        (@ZSMul.toSMul.{0} V
                          (@SubNegMonoid.toZSMul.{0} V
                            (@AddGroup.toSubNegMonoid.{0} V
                              (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                      u a)))))
            (@Set.encard.{0} V
              (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                (@instHVAdd.{0, 0} V (Set.{0} V)
                  (@Set.vaddSet.{0, 0} V V
                    (@instVAddOfAdd.{0} V
                      (@AddZero.toAdd.{0} V
                        (@AddZeroClass.toAddZero.{0} V
                          (@AddMonoid.toAddZeroClass.{0} V
                            (@SubNegMonoid.toAddMonoid.{0} V
                              (@AddGroup.toSubNegMonoid.{0} V
                                (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                a
                (@SetLike.coe.{0, 0}
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  V
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                    ρ))))
            (@Set.encard_exchange.{0} V
              (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                (@instHVAdd.{0, 0} V (Set.{0} V)
                  (@Set.vaddSet.{0, 0} V V
                    (@instVAddOfAdd.{0} V
                      (@AddZero.toAdd.{0} V
                        (@AddZeroClass.toAddZero.{0} V
                          (@AddMonoid.toAddZeroClass.{0} V
                            (@SubNegMonoid.toAddMonoid.{0} V
                              (@AddGroup.toSubNegMonoid.{0} V
                                (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                a
                (@SetLike.coe.{0, 0}
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  V
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ)))
              v
              (@HSMul.hSMul.{0, 0, 0} Int V V
                (@instHSMul.{0, 0} Int V
                  (@ZSMul.toSMul.{0} V
                    (@SubNegMonoid.toZSMul.{0} V
                      (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                u a)
              h_15
              (@mem_of_le_of_mem.{0, 0} (Set.{0} V) V (@Set.instMembership.{0} V)
                (@Preorder.toLE.{0} (Set.{0} V)
                  (@PartialOrder.toPreorder.{0} (Set.{0} V)
                    (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} V)
                      (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} V)
                        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} V)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} V)
                            (@Set.instCompleteAtomicBooleanAlgebra.{0} V)))))))
                (instIsConcreteLESet.{0} V)
                (@SetLike.coe.{0, 0}
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  V
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ))
                (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                  (@instHVAdd.{0, 0} V (Set.{0} V)
                    (@Set.vaddSet.{0, 0} V V
                      (@instVAddOfAdd.{0} V
                        (@AddZero.toAdd.{0} V
                          (@AddZeroClass.toAddZero.{0} V
                            (@AddMonoid.toAddZeroClass.{0} V
                              (@SubNegMonoid.toAddMonoid.{0} V
                                (@AddGroup.toSubNegMonoid.{0} V
                                  (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                  a
                  (@SetLike.coe.{0, 0}
                    (@Submodule.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    V
                    (@Submodule.setLike.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                      ρ)))
                (@Eq.superset.{0} (Set.{0} V) (Set.instUsesSetNotationForOrder.{0} V)
                  (@PartialOrder.toPreorder.{0} (Set.{0} V)
                    (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} V)
                      (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} V)
                        (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} V)
                          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} V)
                            (@Set.instCompleteAtomicBooleanAlgebra.{0} V))))))
                  (@HVAdd.hVAdd.{0, 0, 0} V (Set.{0} V) (Set.{0} V)
                    (@instHVAdd.{0, 0} V (Set.{0} V)
                      (@Set.vaddSet.{0, 0} V V
                        (@instVAddOfAdd.{0} V
                          (@AddZero.toAdd.{0} V
                            (@AddZeroClass.toAddZero.{0} V
                              (@AddMonoid.toAddZeroClass.{0} V
                                (@SubNegMonoid.toAddMonoid.{0} V
                                  (@AddGroup.toSubNegMonoid.{0} V
                                    (@AddCommGroup.toAddGroup.{0} V inst_6)))))))))
                    a
                    (@SetLike.coe.{0, 0}
                      (@Submodule.{0, 0} k V
                        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                      V
                      (@Submodule.setLike.{0, 0} k V
                        (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                      (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                        ρ)))
                  (@SetLike.coe.{0, 0}
                    (@Submodule.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    V
                    (@Submodule.setLike.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7
                      ρ))
                  (@vadd_coe_set.{0, 0} V
                    (@Submodule.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    (@AddCommGroup.toAddGroup.{0} V inst_6)
                    (@Submodule.setLike.{0, 0} k V
                      (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                      (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                    (@Submodule.addSubgroupClass.{0, 0} k V (@CommRing.toRing.{0} k inst_4) inst_6
                      inst_7)
                    (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ)
                    a
                    (@Representation.Coinvariants.mem_ker_of_eq.{0, 0, 0} k G V inst_4 inst_5 inst_6
                      inst_7 ρ g x a h)))
                (@HSMul.hSMul.{0, 0, 0} Int V V
                  (@instHSMul.{0, 0} Int V
                    (@ZSMul.toSMul.{0} V
                      (@SubNegMonoid.toZSMul.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6)))))
                  u a)
                (@zsmul_mem.{0, 0} V
                  (@Submodule.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_6))
                  (@Submodule.setLike.{0, 0} k V
                    (@CommSemiring.toSemiring.{0} k (@CommRing.toCommSemiring.{0} k inst_4))
                    (@AddCommGroup.toAddCommMonoid.{0} V inst_6) inst_7)
                  (@Submodule.addSubgroupClass.{0, 0} k V (@CommRing.toRing.{0} k inst_4) inst_6
                    inst_7)
                  (@Representation.Coinvariants.ker.{0, 0, 0} k G V inst_4 inst_5 inst_6 inst_7 ρ) a
                  (@Representation.Coinvariants.mem_ker_of_eq.{0, 0, 0} k G V inst_4 inst_5 inst_6
                    inst_7 ρ g x a h)
                  u))))))
  -- Phase 1: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_1 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_1 : (17 : Nat) = 17 ∨ (17 : Nat) < 17 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 17)
    cases h_dich_1 with
    | inr h_contra_1 => exact False.elim (Nat.lt_irrefl 17 h_contra_1)
    | inl h_refl_1 => exact (And.intro hp h_refl_1).1
  have h_stage_1 := h_ord_1 h_core
  -- Phase 2: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_2 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_2 : (9 + 5 : Nat) = 14 then
      have h_pack_2 := And.intro h_arith_2 hp
      exact h_pack_2.2
    else
      exact False.elim (h_arith_2 rfl)
  have h_stage_2 := h_chk_2 h_stage_1
  -- Phase 3: Inductive case-analysis ceremony on a trivial index
  have h_lift_3 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_3 := h_lift_3 h_stage_2 0 rfl
  -- Phase 4: Inductive case-analysis ceremony on a trivial index
  have h_lift_4 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_4 := h_lift_4 h_stage_3 0 rfl
  -- Final step: conclude after 4 auxiliary verification stage(s)
  exact id h_stage_4
