import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Disjoint
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.SuccPred
import Mathlib.Order.Lattice
import Mathlib.Order.ModularLattice
import Mathlib.Order.RelClasses
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.SuccPred.Nat
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: FDRep.isIntegral_character (FDRep)
-- Step 1: minpoly.natDegree_pos (minpoly)
-- Step 2: Set.insert_Ioc_pred_right_eq_Ioc (Set)
-- Step 3: Eq.superset (Eq)
-- Step 4: Disjoint.mono (Disjoint)
-- Step 6: Disjoint.inter_left (Disjoint)
-- Step 12: Disjoint.exists_isCompl (Disjoint)
theorem akcm_2026_0028
    {k : Type}
    [inst_2 : Field.{0} k]
    {G : Type}
    [inst_4 : Group.{0} G]
    [inst_5 : Finite.{1} G]
    (V : @FDRep.{0, 0} k G (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
  (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)))
    (g : G)
    {u : Set.{0} Nat}
    {v : Set.{0} Nat}
    (h_10 : @LE.le.{0} (Set.{0} Nat)
  (@Preorder.toLE.{0} (Set.{0} Nat)
    (@PartialOrder.toPreorder.{0} (Set.{0} Nat)
      (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} Nat)
        (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} Nat)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
              (Set.{0} Nat) (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))))
  u v)
    (h_11 : @Disjoint.{0} (Set.{0} Nat)
  (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} Nat)
    (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} Nat)
      (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
        (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
          (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))
  (@HeytingAlgebra.toOrderBot.{0} (Set.{0} Nat)
    (@Order.Frame.toHeytingAlgebra.{0} (Set.{0} Nat)
      (@CompleteDistribLattice.toFrame.{0} (Set.{0} Nat)
        (@CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (Set.{0} Nat)
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
            (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat))))))
  (@insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
    (@Polynomial.natDegree.{0} Int
      (@CommSemiring.toSemiring.{0} Int
        (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
      (@minpoly.{0, 0} Int k Int.instCommRing
        (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
        (@Ring.toIntAlgebra.{0} k
          (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
        (@FDRep.character.{0, 0} k inst_2 G
          (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g)))
    (@Set.Ioc.{0} Nat
      (@PartialOrder.toPreorder.{0} Nat
        (@SemilatticeSup.toPartialOrder.{0} Nat
          (@Lattice.toSemilatticeSup.{0} Nat
            (@DistribLattice.toLattice.{0} Nat
              (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Order.pred.{0} Nat
        (@PartialOrder.toPreorder.{0} Nat
          (@SemilatticeSup.toPartialOrder.{0} Nat
            (@Lattice.toSemilatticeSup.{0} Nat
              (@DistribLattice.toLattice.{0} Nat
                (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
        Nat.instPredOrder
        (@Polynomial.natDegree.{0} Int
          (@CommSemiring.toSemiring.{0} Int
            (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
          (@minpoly.{0, 0} Int k Int.instCommRing
            (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
            (@Ring.toIntAlgebra.{0} k
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
            (@FDRep.character.{0, 0} k inst_2 G
              (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V
              g))))))
  v) :
    ∃ a',
  And
    (@LE.le.{0} (Set.{0} Nat)
      (@Preorder.toLE.{0} (Set.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Set.{0} Nat)
          (@SemilatticeInf.toPartialOrder.{0} (Set.{0} Nat)
            (@Lattice.toSemilatticeInf.{0} (Set.{0} Nat)
              (@ConditionallyCompleteLattice.toLattice.{0} (Set.{0} Nat)
                (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} Nat)
                  (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
                    (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                      (Set.{0} Nat)
                      (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))))))
      (@min.{0} (Set.{0} Nat) (@Set.instMin.{0} Nat)
        (@Set.Ioc.{0} Nat
          (@PartialOrder.toPreorder.{0} Nat
            (@SemilatticeSup.toPartialOrder.{0} Nat
              (@Lattice.toSemilatticeSup.{0} Nat
                (@DistribLattice.toLattice.{0} Nat
                  (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@Polynomial.natDegree.{0} Int
            (@CommSemiring.toSemiring.{0} Int
              (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
            (@minpoly.{0, 0} Int k Int.instCommRing
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
              (@Ring.toIntAlgebra.{0} k
                (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
              (@FDRep.character.{0, 0} k inst_2 G
                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V
                g))))
        v)
      a')
    (@IsCompl.{0} (Set.{0} Nat)
      (@SemilatticeInf.toPartialOrder.{0} (Set.{0} Nat)
        (@Lattice.toSemilatticeInf.{0} (Set.{0} Nat)
          (@ConditionallyCompleteLattice.toLattice.{0} (Set.{0} Nat)
            (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} Nat)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
                  (Set.{0} Nat) (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))))
      (@Set.instBoundedOrder.{0} Nat) a' u) :=   @Disjoint.exists_isCompl.{0} (Set.{0} Nat)
  (@ConditionallyCompleteLattice.toLattice.{0} (Set.{0} Nat)
    (@CompleteLattice.toConditionallyCompleteLattice.{0} (Set.{0} Nat)
      (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
        (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
          (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))
  (@DistribLattice.instIsModularLattice.{0} (Set.{0} Nat) (@Set.instDistribLattice.{0} Nat))
  (@Set.instBoundedOrder.{0} Nat)
  (@BooleanAlgebra.toComplementedLattice.{0} (Set.{0} Nat) (@Set.instBooleanAlgebra.{0} Nat))
  (@min.{0} (Set.{0} Nat) (@Set.instMin.{0} Nat)
    (@Set.Ioc.{0} Nat
      (@PartialOrder.toPreorder.{0} Nat
        (@SemilatticeSup.toPartialOrder.{0} Nat
          (@Lattice.toSemilatticeSup.{0} Nat
            (@DistribLattice.toLattice.{0} Nat
              (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Polynomial.natDegree.{0} Int
        (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
        (@minpoly.{0, 0} Int k Int.instCommRing
          (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
          (@Ring.toIntAlgebra.{0} k
            (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
          (@FDRep.character.{0, 0} k inst_2 G
            (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g))))
    v)
  u
  (@Disjoint.inter_left.{0} Nat
    (@Set.Ioc.{0} Nat
      (@PartialOrder.toPreorder.{0} Nat
        (@SemilatticeSup.toPartialOrder.{0} Nat
          (@Lattice.toSemilatticeSup.{0} Nat
            (@DistribLattice.toLattice.{0} Nat
              (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Polynomial.natDegree.{0} Int
        (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
        (@minpoly.{0, 0} Int k Int.instCommRing
          (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
          (@Ring.toIntAlgebra.{0} k
            (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
          (@FDRep.character.{0, 0} k inst_2 G
            (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g))))
    u v
    (@Disjoint.mono.{0} (Set.{0} Nat)
      (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} Nat)
        (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} Nat)
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
              (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat)))))
      (@HeytingAlgebra.toOrderBot.{0} (Set.{0} Nat)
        (@Order.Frame.toHeytingAlgebra.{0} (Set.{0} Nat)
          (@CompleteDistribLattice.toFrame.{0} (Set.{0} Nat)
            (@CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (Set.{0} Nat)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
                (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat))))))
      (@Set.Ioc.{0} Nat
        (@PartialOrder.toPreorder.{0} Nat
          (@SemilatticeSup.toPartialOrder.{0} Nat
            (@Lattice.toSemilatticeSup.{0} Nat
              (@DistribLattice.toLattice.{0} Nat
                (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Polynomial.natDegree.{0} Int
          (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
          (@minpoly.{0, 0} Int k Int.instCommRing
            (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
            (@Ring.toIntAlgebra.{0} k
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
            (@FDRep.character.{0, 0} k inst_2 G
              (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g))))
      (@insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
        (@Polynomial.natDegree.{0} Int
          (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
          (@minpoly.{0, 0} Int k Int.instCommRing
            (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
            (@Ring.toIntAlgebra.{0} k
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
            (@FDRep.character.{0, 0} k inst_2 G
              (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g)))
        (@Set.Ioc.{0} Nat
          (@PartialOrder.toPreorder.{0} Nat
            (@SemilatticeSup.toPartialOrder.{0} Nat
              (@Lattice.toSemilatticeSup.{0} Nat
                (@DistribLattice.toLattice.{0} Nat
                  (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@Order.pred.{0} Nat
            (@PartialOrder.toPreorder.{0} Nat
              (@SemilatticeSup.toPartialOrder.{0} Nat
                (@Lattice.toSemilatticeSup.{0} Nat
                  (@DistribLattice.toLattice.{0} Nat
                    (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
            Nat.instPredOrder
            (@Polynomial.natDegree.{0} Int
              (@CommSemiring.toSemiring.{0} Int
                (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
              (@minpoly.{0, 0} Int k Int.instCommRing
                (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
                (@Ring.toIntAlgebra.{0} k
                  (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
                (@FDRep.character.{0, 0} k inst_2 G
                  (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g))))))
      u v
      (@Eq.superset.{0} (Set.{0} Nat) (Set.instUsesSetNotationForOrder.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Set.{0} Nat)
          (@ChainCompletePartialOrder.toPartialOrder.{0} (Set.{0} Nat)
            (@ChainCompletePartialOrder.instOfCompleteLattice.{0} (Set.{0} Nat)
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} Nat)
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} Nat)
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} Nat))))))
        (@insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
          (@Polynomial.natDegree.{0} Int
            (@CommSemiring.toSemiring.{0} Int
              (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
            (@minpoly.{0, 0} Int k Int.instCommRing
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
              (@Ring.toIntAlgebra.{0} k
                (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
              (@FDRep.character.{0, 0} k inst_2 G
                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g)))
          (@Set.Ioc.{0} Nat
            (@PartialOrder.toPreorder.{0} Nat
              (@SemilatticeSup.toPartialOrder.{0} Nat
                (@Lattice.toSemilatticeSup.{0} Nat
                  (@DistribLattice.toLattice.{0} Nat
                    (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Order.pred.{0} Nat
              (@PartialOrder.toPreorder.{0} Nat
                (@SemilatticeSup.toPartialOrder.{0} Nat
                  (@Lattice.toSemilatticeSup.{0} Nat
                    (@DistribLattice.toLattice.{0} Nat
                      (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
              Nat.instPredOrder
              (@Polynomial.natDegree.{0} Int
                (@CommSemiring.toSemiring.{0} Int
                  (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
                (@minpoly.{0, 0} Int k Int.instCommRing
                  (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
                  (@Ring.toIntAlgebra.{0} k
                    (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
                  (@FDRep.character.{0, 0} k inst_2 G
                    (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V
                    g))))))
        (@Set.Ioc.{0} Nat
          (@PartialOrder.toPreorder.{0} Nat
            (@SemilatticeSup.toPartialOrder.{0} Nat
              (@Lattice.toSemilatticeSup.{0} Nat
                (@DistribLattice.toLattice.{0} Nat
                  (@instDistribLatticeOfLinearOrder.{0} Nat Nat.instLinearOrder)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@Polynomial.natDegree.{0} Int
            (@CommSemiring.toSemiring.{0} Int
              (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
            (@minpoly.{0, 0} Int k Int.instCommRing
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
              (@Ring.toIntAlgebra.{0} k
                (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
              (@FDRep.character.{0, 0} k inst_2 G
                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g))))
        (@Set.insert_Ioc_pred_right_eq_Ioc.{0} Nat Nat.instLinearOrder Nat.instPredOrder
          (@Polynomial.natDegree.{0} Int
            (@CommSemiring.toSemiring.{0} Int
              (@CommRing.toCommSemiring.{0} Int Int.instCommRing))
            (@minpoly.{0, 0} Int k Int.instCommRing
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
              (@Ring.toIntAlgebra.{0} k
                (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
              (@FDRep.character.{0, 0} k inst_2 G
                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@minpoly.natDegree_pos.{0, 0} Int k Int.instCommRing
            (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2))
            (@Ring.toIntAlgebra.{0} k
              (@DivisionRing.toRing.{0} k (@Field.toDivisionRing.{0} k inst_2)))
            (@FDRep.character.{0, 0} k inst_2 G
              (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst_4)) V g)
            (@IsLocalRing.toNontrivial.{0} k
              (@CommSemiring.toSemiring.{0} k
                (@Semifield.toCommSemiring.{0} k (@Field.toSemifield.{0} k inst_2)))
              (@Field.instIsLocalRing.{0} k inst_2))
            (@FDRep.isIntegral_character.{0, 0} k inst_2 G inst_4 inst_5 V g))))
      h_10 h_11))
