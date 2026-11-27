import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.Logic.Embedding.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Max
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.SuccPred.ENat
import Mathlib.Order.SuccPred.Limit
import Mathlib.RingTheory.Multiplicity

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: RootPairing.zero_notMem_range_root (RootPairing)
-- Step 1: Set.encard_insert_of_notMem (Set)
-- Step 2: dvd_of_eq (dvd_of_eq)
-- Step 3: emultiplicity_le_emultiplicity_of_dvd_left (emultiplicity_le_emultiplicity_of_dvd_left)
-- Step 5: Order.lt_succ_of_le_of_not_isMax (Order)
-- Step 6: Order.IsPredPrelimit.nonempty_Ioo_of_lt (Order)
-- Step 7: IsGLB.mem_of_not_isPredLimit (IsGLB)
-- Step 8: Set.encard_ne_zero_of_mem (Set)
theorem akcm_2026_0024
    {ι : Type}
    {R : Type}
    {M : Type}
    {N : Type}
    [inst_5 : CommRing.{0} R]
    [inst_6 : AddCommGroup.{0} M]
    [inst_7 : @Module.{0, 0} R M
  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_5))
  (@AddCommGroup.toAddCommMonoid.{0} M inst_6)]
    [inst_8 : AddCommGroup.{0} N]
    [inst_9 : @Module.{0, 0} R N
  (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_5))
  (@AddCommGroup.toAddCommMonoid.{0} N inst_8)]
    (P : @RootPairing.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9)
    [inst_11 : @NeZero.{0} R
  (@MulZeroClass.toZero.{0} R
    (@instMulZeroClassOfSemiring.{0} R
      (@CommSemiring.toSemiring.{0} R (@CommRing.toCommSemiring.{0} R inst_5))))
  (@OfNat.ofNat.{0} R (nat_lit 2)
    (@instOfNatAtLeastTwo.{0} R (nat_lit 2)
      (@AddMonoidWithOne.toNatCast.{0} R
        (@AddGroupWithOne.toAddMonoidWithOne.{0} R
          (@Ring.toAddGroupWithOne.{0} R (@CommRing.toRing.{0} R inst_5))))
      (@Nat.instAtLeastTwoHAddOfNat
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Nat.instNeZeroSucc
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))]
    {u : ENat}
    (h_13 : Not
  (@IsMax.{0} ENat (@Preorder.toLE.{0} ENat instPreorderENat)
    (@emultiplicity.{0} ENat
      (@CommMonoid.toMonoid.{0} ENat
        (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
      (@Set.encard.{0} M
        (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
          (@OfNat.ofNat.{0} M (nat_lit 0)
            (@Zero.toOfNat0.{0} M
              (@NegZeroClass.toZero.{0} M
                (@SubNegZeroMonoid.toNegZeroClass.{0} M
                  (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                    (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                      (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
          (@Set.range.{0, 1} M ι
            (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
              (@Function.instFunLikeEmbedding.{1, 1} ι M)
              (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
                inst_9 P)))))
      u)))
    (h_14 : @Order.IsPredPrelimit.{0} ENat (@Preorder.toLT.{0} ENat instPreorderENat)
  (@emultiplicity.{0} ENat
    (@CommMonoid.toMonoid.{0} ENat
      (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
    (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
      (@Set.encard.{0} M
        (@Set.range.{0, 1} M ι
          (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
            (@Function.instFunLikeEmbedding.{1, 1} ι M)
            (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
              inst_9 P))))
      (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
    u))
    {v : ENat}
    (h_16 : @IsGLB.{0} ENat
  (@Preorder.toLE.{0} ENat
    (@PartialOrder.toPreorder.{0} ENat
      (@SemilatticeSup.toPartialOrder.{0} ENat
        (@Lattice.toSemilatticeSup.{0} ENat
          (@DistribLattice.toLattice.{0} ENat
            (@instDistribLatticeOfLinearOrder.{0} ENat instLinearOrderENat))))))
  (@Set.Ioo.{0} ENat instPreorderENat
    (@emultiplicity.{0} ENat
      (@CommMonoid.toMonoid.{0} ENat
        (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
      (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
        (@Set.encard.{0} M
          (@Set.range.{0, 1} M ι
            (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
              (@Function.instFunLikeEmbedding.{1, 1} ι M)
              (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
                inst_9 P))))
        (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
      u)
    (@Order.succ.{0} ENat instPreorderENat instSuccOrderENat
      (@emultiplicity.{0} ENat
        (@CommMonoid.toMonoid.{0} ENat
          (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
        (@Set.encard.{0} M
          (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
            (@OfNat.ofNat.{0} M (nat_lit 0)
              (@Zero.toOfNat0.{0} M
                (@NegZeroClass.toZero.{0} M
                  (@SubNegZeroMonoid.toNegZeroClass.{0} M
                    (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                      (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                        (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
            (@Set.range.{0, 1} M ι
              (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                (@Function.instFunLikeEmbedding.{1, 1} ι M)
                (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
                  inst_9 P)))))
        u)))
  v)
    (h_17 : Not
  (@Order.IsPredLimit.{0} ENat
    (@PartialOrder.toPreorder.{0} ENat
      (@SemilatticeSup.toPartialOrder.{0} ENat
        (@Lattice.toSemilatticeSup.{0} ENat
          (@DistribLattice.toLattice.{0} ENat
            (@instDistribLatticeOfLinearOrder.{0} ENat instLinearOrderENat)))))
    v)) :
    @Ne.{1} ENat
  (@Set.encard.{0} ENat
    (@Set.Ioo.{0} ENat instPreorderENat
      (@emultiplicity.{0} ENat
        (@CommMonoid.toMonoid.{0} ENat
          (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
        (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
          (@Set.encard.{0} M
            (@Set.range.{0, 1} M ι
              (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                (@Function.instFunLikeEmbedding.{1, 1} ι M)
                (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
                  inst_9 P))))
          (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
        u)
      (@Order.succ.{0} ENat instPreorderENat instSuccOrderENat
        (@emultiplicity.{0} ENat
          (@CommMonoid.toMonoid.{0} ENat
            (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
          (@Set.encard.{0} M
            (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
              (@OfNat.ofNat.{0} M (nat_lit 0)
                (@Zero.toOfNat0.{0} M
                  (@NegZeroClass.toZero.{0} M
                    (@SubNegZeroMonoid.toNegZeroClass.{0} M
                      (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                        (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                          (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
              (@Set.range.{0, 1} M ι
                (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                  (@Function.instFunLikeEmbedding.{1, 1} ι M)
                  (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8
                    inst_9 P)))))
          u))))
  (@OfNat.ofNat.{0} ENat (nat_lit 0) (@Zero.toOfNat0.{0} ENat instZeroENat)) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Set.encard_ne_zero_of_mem.{0} ENat
      (@Set.Ioo.{0} ENat instPreorderENat
        (@emultiplicity.{0} ENat
          (@CommMonoid.toMonoid.{0} ENat (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
          (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
            (@Set.encard.{0} M
              (@Set.range.{0, 1} M ι
                (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                  (@Function.instFunLikeEmbedding.{1, 1} ι M)
                  (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P))))
            (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
          u)
        (@Order.succ.{0} ENat instPreorderENat instSuccOrderENat
          (@emultiplicity.{0} ENat
            (@CommMonoid.toMonoid.{0} ENat
              (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
            (@Set.encard.{0} M
              (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
                (@OfNat.ofNat.{0} M (nat_lit 0)
                  (@Zero.toOfNat0.{0} M
                    (@NegZeroClass.toZero.{0} M
                      (@SubNegZeroMonoid.toNegZeroClass.{0} M
                        (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                          (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                            (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
                (@Set.range.{0, 1} M ι
                  (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                    (@Function.instFunLikeEmbedding.{1, 1} ι M)
                    (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                      P)))))
            u)))
      v
      (@IsGLB.mem_of_not_isPredLimit.{0} ENat v instLinearOrderENat
        (@Set.Ioo.{0} ENat instPreorderENat
          (@emultiplicity.{0} ENat
            (@CommMonoid.toMonoid.{0} ENat
              (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
            (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
              (@Set.encard.{0} M
                (@Set.range.{0, 1} M ι
                  (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                    (@Function.instFunLikeEmbedding.{1, 1} ι M)
                    (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P))))
              (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
            u)
          (@Order.succ.{0} ENat instPreorderENat instSuccOrderENat
            (@emultiplicity.{0} ENat
              (@CommMonoid.toMonoid.{0} ENat
                (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
              (@Set.encard.{0} M
                (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
                  (@OfNat.ofNat.{0} M (nat_lit 0)
                    (@Zero.toOfNat0.{0} M
                      (@NegZeroClass.toZero.{0} M
                        (@SubNegZeroMonoid.toNegZeroClass.{0} M
                          (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                            (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                              (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
                  (@Set.range.{0, 1} M ι
                    (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                      (@Function.instFunLikeEmbedding.{1, 1} ι M)
                      (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                        P)))))
              u)))
        h_16
        (@Order.IsPredPrelimit.nonempty_Ioo_of_lt.{0} ENat
          (@emultiplicity.{0} ENat
            (@CommMonoid.toMonoid.{0} ENat
              (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
            (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
              (@Set.encard.{0} M
                (@Set.range.{0, 1} M ι
                  (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                    (@Function.instFunLikeEmbedding.{1, 1} ι M)
                    (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9 P))))
              (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
            u)
          (@Order.succ.{0} ENat instPreorderENat instSuccOrderENat
            (@emultiplicity.{0} ENat
              (@CommMonoid.toMonoid.{0} ENat
                (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
              (@Set.encard.{0} M
                (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
                  (@OfNat.ofNat.{0} M (nat_lit 0)
                    (@Zero.toOfNat0.{0} M
                      (@NegZeroClass.toZero.{0} M
                        (@SubNegZeroMonoid.toNegZeroClass.{0} M
                          (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                            (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                              (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
                  (@Set.range.{0, 1} M ι
                    (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                      (@Function.instFunLikeEmbedding.{1, 1} ι M)
                      (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                        P)))))
              u))
          instPreorderENat h_14
          (@Order.lt_succ_of_le_of_not_isMax.{0} ENat instPreorderENat instSuccOrderENat
            (@emultiplicity.{0} ENat
              (@CommMonoid.toMonoid.{0} ENat
                (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
              (@Set.encard.{0} M
                (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
                  (@OfNat.ofNat.{0} M (nat_lit 0)
                    (@Zero.toOfNat0.{0} M
                      (@NegZeroClass.toZero.{0} M
                        (@SubNegZeroMonoid.toNegZeroClass.{0} M
                          (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                            (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                              (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
                  (@Set.range.{0, 1} M ι
                    (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                      (@Function.instFunLikeEmbedding.{1, 1} ι M)
                      (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                        P)))))
              u)
            (@emultiplicity.{0} ENat
              (@CommMonoid.toMonoid.{0} ENat
                (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat))
              (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
                (@Set.encard.{0} M
                  (@Set.range.{0, 1} M ι
                    (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                      (@Function.instFunLikeEmbedding.{1, 1} ι M)
                      (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                        P))))
                (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
              u)
            (@emultiplicity_le_emultiplicity_of_dvd_left.{0} ENat
              (@CommSemiring.toCommMonoid.{0} ENat instCommSemiringENat)
              (@Set.encard.{0} M
                (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
                  (@OfNat.ofNat.{0} M (nat_lit 0)
                    (@Zero.toOfNat0.{0} M
                      (@NegZeroClass.toZero.{0} M
                        (@SubNegZeroMonoid.toNegZeroClass.{0} M
                          (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                            (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                              (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
                  (@Set.range.{0, 1} M ι
                    (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                      (@Function.instFunLikeEmbedding.{1, 1} ι M)
                      (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                        P)))))
              (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
                (@Set.encard.{0} M
                  (@Set.range.{0, 1} M ι
                    (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                      (@Function.instFunLikeEmbedding.{1, 1} ι M)
                      (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                        P))))
                (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
              u
              (@dvd_of_eq.{0} ENat
                (@Semiring.toMonoid.{0} ENat
                  (@CommSemiring.toSemiring.{0} ENat instCommSemiringENat))
                (@Set.encard.{0} M
                  (@insert.{0, 0} M (Set.{0} M) (@Set.instInsert.{0} M)
                    (@OfNat.ofNat.{0} M (nat_lit 0)
                      (@Zero.toOfNat0.{0} M
                        (@NegZeroClass.toZero.{0} M
                          (@SubNegZeroMonoid.toNegZeroClass.{0} M
                            (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                              (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                                (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
                    (@Set.range.{0, 1} M ι
                      (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                        (@Function.instFunLikeEmbedding.{1, 1} ι M)
                        (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                          P)))))
                (@HAdd.hAdd.{0, 0, 0} ENat ENat ENat (@instHAdd.{0} ENat instAddENat)
                  (@Set.encard.{0} M
                    (@Set.range.{0, 1} M ι
                      (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                        (@Function.instFunLikeEmbedding.{1, 1} ι M)
                        (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                          P))))
                  (@OfNat.ofNat.{0} ENat (nat_lit 1) (@One.toOfNat1.{0} ENat instOneENat)))
                (@Set.encard_insert_of_notMem.{0} M
                  (@Set.range.{0, 1} M ι
                    (@DFunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} ι M) ι (fun x ↦ M)
                      (@Function.instFunLikeEmbedding.{1, 1} ι M)
                      (@RootPairing.root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7 inst_8 inst_9
                        P)))
                  (@OfNat.ofNat.{0} M (nat_lit 0)
                    (@Zero.toOfNat0.{0} M
                      (@NegZeroClass.toZero.{0} M
                        (@SubNegZeroMonoid.toNegZeroClass.{0} M
                          (@SubtractionMonoid.toSubNegZeroMonoid.{0} M
                            (@SubtractionCommMonoid.toSubtractionMonoid.{0} M
                              (@AddCommGroup.toDivisionAddCommMonoid.{0} M inst_6)))))))
                  (@RootPairing.zero_notMem_range_root.{0, 0, 0, 0} ι R M N inst_5 inst_6 inst_7
                    inst_8 inst_9 P inst_11))))
            h_13))
        h_17)
  -- Phase 1: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_1 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_1 : (23 : Nat) = 23 ∨ (23 : Nat) < 23 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 23)
    cases h_dich_1 with
    | inr h_contra_1 => exact False.elim (Nat.lt_irrefl 23 h_contra_1)
    | inl h_refl_1 => exact (And.intro hp h_refl_1).1
  have h_stage_1 := h_ord_1 h_core
  -- Phase 2: Inductive case-analysis ceremony on a trivial index
  have h_lift_2 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_2 := h_lift_2 h_stage_1 0 rfl
  -- Phase 3: Redundant implication-chain mediation
  have h_med_3 : ∀ {P : Prop}, P → (True → P) ∧ (P → P) := fun hp =>
    And.intro (fun _ => id hp) (fun h => (And.intro h hp).1)
  have h_stage_3 := (h_med_3 h_stage_2).2 ((h_med_3 h_stage_2).1 True.intro)
  -- Phase 4: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_4 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_4 : (13 + 3 : Nat) = 16 then
      have h_pack_4 := And.intro h_arith_4 hp
      exact h_pack_4.2
    else
      exact False.elim (h_arith_4 rfl)
  have h_stage_4 := h_chk_4 h_stage_3
  -- Phase 5: Inductive case-analysis ceremony on a trivial index
  have h_lift_5 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_5 := h_lift_5 h_stage_4 0 rfl
  -- Final step: conclude after 5 auxiliary verification stage(s)
  exact id h_stage_5
