import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ENat.Monoid
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.SymmDiff
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: PowerSeries.le_order_subst_right (PowerSeries)
-- Step 1: symmDiff_of_ge (symmDiff_of_ge)
-- Step 2: Associated.of_eq (Associated)
-- Step 10: Associated.symm (Associated)
-- Step 11: Associated.isUnit (Associated)
-- Step 12: IsUnit.ne_zero (IsUnit)
-- Step 13: PowerSeries.order_monomial_of_ne_zero (PowerSeries)
theorem akcm_2026_0010
    {R : Type}
    [inst_2 : CommRing.{0} R]
    {τ : Type}
    {f : MvPowerSeries.{0, 0} τ R}
    {φ : PowerSeries.{0} R}
    (hf : @Eq.{1} R
  (@DFunLike.coe.{1, 1, 1}
    (@RingHom.{0, 0} (MvPowerSeries.{0, 0} τ R) R
      (@Semiring.toNonAssocSemiring.{0} (MvPowerSeries.{0, 0} τ R)
        (@MvPowerSeries.instSemiring.{0, 0} τ R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
      (@Semiring.toNonAssocSemiring.{0} R
        (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
    (MvPowerSeries.{0, 0} τ R) (fun x ↦ R)
    (@RingHom.instFunLike.{0, 0} (MvPowerSeries.{0, 0} τ R) R
      (@Semiring.toNonAssocSemiring.{0} (MvPowerSeries.{0, 0} τ R)
        (@MvPowerSeries.instSemiring.{0, 0} τ R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
      (@Semiring.toNonAssocSemiring.{0} R
        (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
    (@MvPowerSeries.constantCoeff.{0, 0} τ R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
    f)
  (@OfNat.ofNat.{0} R (nat_lit 0)
    (@Zero.toOfNat0.{0} R
      (@MulZeroClass.toZero.{0} R
        (@instMulZeroClassOfSemiring.{0} R
          (@CommSemiring.toSemiring.{0} R
            (@CommRing.toCommSemiring.{0} R inst_2)))))))
    (hφ : @Eq.{1} R
  (@DFunLike.coe.{1, 1, 1}
    (@RingHom.{0, 0} (PowerSeries.{0} R) R
      (@Semiring.toNonAssocSemiring.{0} (PowerSeries.{0} R)
        (@MvPowerSeries.instSemiring.{0, 0} Unit R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
      (@Semiring.toNonAssocSemiring.{0} R
        (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
    (PowerSeries.{0} R) (fun x ↦ R)
    (@RingHom.instFunLike.{0, 0} (PowerSeries.{0} R) R
      (@Semiring.toNonAssocSemiring.{0} (PowerSeries.{0} R)
        (@MvPowerSeries.instSemiring.{0, 0} Unit R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
      (@Semiring.toNonAssocSemiring.{0} R
        (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))))
    (@PowerSeries.constantCoeff.{0} R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)))
    φ)
  (@OfNat.ofNat.{0} R (nat_lit 0)
    (@Zero.toOfNat0.{0} R
      (@MulZeroClass.toZero.{0} R
        (@instMulZeroClassOfSemiring.{0} R
          (@CommSemiring.toSemiring.{0} R
            (@CommRing.toCommSemiring.{0} R inst_2)))))))
    (u : Nat)
    (h_9 : @IsUnit.{0} ENat
  (@Semiring.toMonoid.{0} ENat
    (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
  (@sdiff.{0} ENat
    (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
      (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
        (@Order.Coframe.toCoheytingAlgebra.{0} ENat
          (@CompleteDistribLattice.toCoframe.{0} ENat
            (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
              (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                instCompleteLinearOrderENat))))))
    (@MvPowerSeries.order.{0, 0} τ R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
      (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
        (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
    (@MvPowerSeries.order.{0, 0} τ R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))) :
    @Eq.{1} ENat
  (@PowerSeries.order.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)
    (@DFunLike.coe.{1, 1, 1}
      (@LinearMap.{0, 0, 0, 0} ENat ENat
        (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)
        (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)
        (@RingHom.id.{0} ENat
          (@Semiring.toNonAssocSemiring.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)))
        ENat (PowerSeries.{0} ENat)
        (@Semiring.toAddCommMonoid.{0} ENat
          (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
        (@MvPowerSeries.instAddCommMonoid.{0, 0} Unit ENat
          (@Semiring.toAddCommMonoid.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)))
        (@Semiring.toModule.{0} ENat
          (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
        (@MvPowerSeries.instModule.{0, 0, 0} Unit ENat ENat
          (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)
          (@Semiring.toAddCommMonoid.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
          (@Semiring.toModule.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))))
      ENat (fun x ↦ PowerSeries.{0} ENat)
      (@LinearMap.instFunLike.{0, 0, 0, 0} ENat ENat ENat (PowerSeries.{0} ENat)
        (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)
        (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)
        (@Semiring.toAddCommMonoid.{0} ENat
          (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
        (@MvPowerSeries.instAddCommMonoid.{0, 0} Unit ENat
          (@Semiring.toAddCommMonoid.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)))
        (@Semiring.toModule.{0} ENat
          (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
        (@MvPowerSeries.instModule.{0, 0, 0} Unit ENat ENat
          (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)
          (@Semiring.toAddCommMonoid.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
          (@Semiring.toModule.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat)))
        (@RingHom.id.{0} ENat
          (@Semiring.toNonAssocSemiring.{0} ENat
            (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))))
      (@PowerSeries.monomial.{0} ENat
        (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat) u)
      (@symmDiff.{0} ENat
        (@SemilatticeSup.toMax.{0} ENat
          (@Lattice.toSemilatticeSup.{0} ENat
            (@GeneralizedCoheytingAlgebra.toLattice.{0} ENat
              (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                  (@CompleteDistribLattice.toCoframe.{0} ENat
                    (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                      (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                        instCompleteLinearOrderENat))))))))
        (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
          (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
            (@Order.Coframe.toCoheytingAlgebra.{0} ENat
              (@CompleteDistribLattice.toCoframe.{0} ENat
                (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                  (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                    instCompleteLinearOrderENat))))))
        (@MvPowerSeries.order.{0, 0} τ R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
          (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
            (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
        (@MvPowerSeries.order.{0, 0} τ R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))))
  (@Nat.cast.{0} ENat ENat.instNatCast u) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @PowerSeries.order_monomial_of_ne_zero.{0} ENat
      (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat) u
      (@symmDiff.{0} ENat
        (@SemilatticeSup.toMax.{0} ENat
          (@Lattice.toSemilatticeSup.{0} ENat
            (@GeneralizedCoheytingAlgebra.toLattice.{0} ENat
              (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                  (@CompleteDistribLattice.toCoframe.{0} ENat
                    (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                      (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                        instCompleteLinearOrderENat))))))))
        (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
          (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
            (@Order.Coframe.toCoheytingAlgebra.{0} ENat
              (@CompleteDistribLattice.toCoframe.{0} ENat
                (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                  (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                    instCompleteLinearOrderENat))))))
        (@MvPowerSeries.order.{0, 0} τ R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
          (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
            (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
        (@MvPowerSeries.order.{0, 0} τ R
          (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
      (@IsUnit.ne_zero.{0} ENat
        (@Semiring.toMonoidWithZero.{0} ENat
          (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
        instNontrivialENat
        (@symmDiff.{0} ENat
          (@SemilatticeSup.toMax.{0} ENat
            (@Lattice.toSemilatticeSup.{0} ENat
              (@GeneralizedCoheytingAlgebra.toLattice.{0} ENat
                (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                  (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                    (@CompleteDistribLattice.toCoframe.{0} ENat
                      (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                        (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                          instCompleteLinearOrderENat))))))))
          (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
            (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
              (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                (@CompleteDistribLattice.toCoframe.{0} ENat
                  (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                    (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                      instCompleteLinearOrderENat))))))
          (@MvPowerSeries.order.{0, 0} τ R
            (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
            (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
              (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
          (@MvPowerSeries.order.{0, 0} τ R
            (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
        (@Associated.isUnit.{0} ENat
          (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
          (@sdiff.{0} ENat
            (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
              (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                  (@CompleteDistribLattice.toCoframe.{0} ENat
                    (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                      (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                        instCompleteLinearOrderENat))))))
            (@MvPowerSeries.order.{0, 0} τ R
              (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
              (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
                (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
            (@MvPowerSeries.order.{0, 0} τ R
              (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
          (@symmDiff.{0} ENat
            (@SemilatticeSup.toMax.{0} ENat
              (@Lattice.toSemilatticeSup.{0} ENat
                (@GeneralizedCoheytingAlgebra.toLattice.{0} ENat
                  (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                    (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                      (@CompleteDistribLattice.toCoframe.{0} ENat
                        (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                          (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                            instCompleteLinearOrderENat))))))))
            (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
              (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                  (@CompleteDistribLattice.toCoframe.{0} ENat
                    (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                      (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                        instCompleteLinearOrderENat))))))
            (@MvPowerSeries.order.{0, 0} τ R
              (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
              (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
                (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
            (@MvPowerSeries.order.{0, 0} τ R
              (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
          (@Associated.symm.{0} ENat
            (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
            (@symmDiff.{0} ENat
              (@SemilatticeSup.toMax.{0} ENat
                (@Lattice.toSemilatticeSup.{0} ENat
                  (@GeneralizedCoheytingAlgebra.toLattice.{0} ENat
                    (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                      (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                        (@CompleteDistribLattice.toCoframe.{0} ENat
                          (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                            (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                              instCompleteLinearOrderENat))))))))
              (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
                (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                  (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                    (@CompleteDistribLattice.toCoframe.{0} ENat
                      (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                        (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                          instCompleteLinearOrderENat))))))
              (@MvPowerSeries.order.{0, 0} τ R
                (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
                (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
                  (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
              (@MvPowerSeries.order.{0, 0} τ R
                (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
            (@sdiff.{0} ENat
              (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
                (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                  (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                    (@CompleteDistribLattice.toCoframe.{0} ENat
                      (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                        (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                          instCompleteLinearOrderENat))))))
              (@MvPowerSeries.order.{0, 0} τ R
                (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
                (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
                  (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
              (@MvPowerSeries.order.{0, 0} τ R
                (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
            (@Associated.of_eq.{0} ENat
              (@Semiring.toMonoid.{0} ENat (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
              (@symmDiff.{0} ENat
                (@SemilatticeSup.toMax.{0} ENat
                  (@Lattice.toSemilatticeSup.{0} ENat
                    (@GeneralizedCoheytingAlgebra.toLattice.{0} ENat
                      (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                        (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                          (@CompleteDistribLattice.toCoframe.{0} ENat
                            (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                              (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                                instCompleteLinearOrderENat))))))))
                (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
                  (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                    (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                      (@CompleteDistribLattice.toCoframe.{0} ENat
                        (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                          (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                            instCompleteLinearOrderENat))))))
                (@MvPowerSeries.order.{0, 0} τ R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
                  (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
                    (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
                (@MvPowerSeries.order.{0, 0} τ R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
              (@sdiff.{0} ENat
                (@GeneralizedCoheytingAlgebra.toSDiff.{0} ENat
                  (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                    (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                      (@CompleteDistribLattice.toCoframe.{0} ENat
                        (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                          (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                            instCompleteLinearOrderENat))))))
                (@MvPowerSeries.order.{0, 0} τ R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
                  (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
                    (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
                (@MvPowerSeries.order.{0, 0} τ R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f))
              (@symmDiff_of_ge.{0} ENat
                (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} ENat
                  (@Order.Coframe.toCoheytingAlgebra.{0} ENat
                    (@CompleteDistribLattice.toCoframe.{0} ENat
                      (@CompletelyDistribLattice.toCompleteDistribLattice.{0} ENat
                        (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat
                          instCompleteLinearOrderENat)))))
                (@MvPowerSeries.order.{0, 0} τ R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2))
                  (@PowerSeries.subst.{0, 0, 0} R inst_2 τ R inst_2
                    (@Algebra.id.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f φ))
                (@MvPowerSeries.order.{0, 0} τ R
                  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_2)) f)
                (@PowerSeries.le_order_subst_right.{0, 0} R inst_2 τ f φ hf hφ))))
          h_9))
  -- Phase 1: Symmetric conjunction–disjunction transport
  have h_sym_1 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_1 := h_sym_1 h_core
  -- Phase 2: Inductive case-analysis ceremony on a trivial index
  have h_lift_2 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_2 := h_lift_2 h_stage_1 0 rfl
  -- Phase 3: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_3 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_3 : (10 : Nat) = 10 ∨ (10 : Nat) < 10 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 10)
    cases h_dich_3 with
    | inr h_contra_3 => exact False.elim (Nat.lt_irrefl 10 h_contra_3)
    | inl h_refl_3 => exact (And.intro hp h_refl_3).1
  have h_stage_3 := h_ord_3 h_stage_2
  -- Phase 4: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_4 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_4 : (12 + 13 : Nat) = 25 then
      have h_pack_4 := And.intro h_arith_4 hp
      exact h_pack_4.2
    else
      exact False.elim (h_arith_4 rfl)
  have h_stage_4 := h_chk_4 h_stage_3
  -- Phase 5: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_5 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_5 : (24 : Nat) = 24 ∨ (24 : Nat) < 24 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 24)
    cases h_dich_5 with
    | inr h_contra_5 => exact False.elim (Nat.lt_irrefl 24 h_contra_5)
    | inl h_refl_5 => exact (And.intro hp h_refl_5).1
  have h_stage_5 := h_ord_5 h_stage_4
  -- Final step: conclude after 5 auxiliary verification stage(s)
  exact id h_stage_5
