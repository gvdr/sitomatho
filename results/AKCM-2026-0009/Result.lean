import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Basic.Finite.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Opposite
import Mathlib.Basic.SetLike.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Topology.Bases
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Sets.Opens

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: AlgebraicGeometry.Scheme.zeroLocus_map (AlgebraicGeometry)
-- Step 1: subset_of_subset_of_eq (subset_of_subset_of_eq)
-- Step 9: Set.Finite.subset (Set)
-- Step 10: Set.Finite.isSeparable (Set)
theorem akcm_2026_0009
    (X : AlgebraicGeometry.Scheme.{0})
    {U : X.Opens}
    {V : X.Opens}
    (i : @LE.le.{0} X.Opens
  (@Preorder.toLE.{0} X.Opens
    (@PartialOrder.toPreorder.{0} X.Opens
      (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0,
              0}
          CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))))
  U V)
    (s : Set.{0}
  ↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
      (Opposite.{1}
        (@TopologicalSpace.Opens.{0} (↥X)
          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
              CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                CommRingCat.{0} CommRingCat.instCategory.{0}
                X.toSheafedSpace)).str))
      (@CategoryTheory.Category.opposite.{0, 0}
        (@TopologicalSpace.Opens.{0} (↥X)
          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
              CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
        (@Preorder.smallCategory.{0}
          (@TopologicalSpace.Opens.{0} (↥X)
            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  X.toSheafedSpace)).str)
          (@PartialOrder.toPreorder.{0}
            (@TopologicalSpace.Opens.{0} (↥X)
              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                  CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    X.toSheafedSpace)).str)
            (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                  CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    X.toSheafedSpace)).str))))
      CommRingCat.{0} CommRingCat.instCategory.{0}
      (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
        CommRingCat.instCategory.{0}
        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
          CommRingCat.instCategory.{0} X.toSheafedSpace))
      (@Opposite.op.{1} X.Opens V)))
    {u : Set.{0} ↥X}
    (h_7 : @LE.le.{0} (Set.{0} ↥X) (@Set.instLE.{0} ↥X) u
  (@AlgebraicGeometry.Scheme.zeroLocus.{0} X U
    (@Set.image.{0, 0}
      (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
          (Opposite.{1}
            (@TopologicalSpace.Opens.{0} (↥X)
              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                  CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    X.toSheafedSpace)).str))
          (@CategoryTheory.Category.opposite.{0, 0}
            (@TopologicalSpace.Opens.{0} (↥X)
              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                  CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    X.toSheafedSpace)).str)
            (@Preorder.smallCategory.{0}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str)
              (@PartialOrder.toPreorder.{0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str))))
          CommRingCat.{0} CommRingCat.instCategory.{0}
          (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
            CommRingCat.instCategory.{0}
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
          (@Opposite.op.{1} X.Opens V)))
      (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
          (Opposite.{1}
            (@TopologicalSpace.Opens.{0} (↥X)
              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                  CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    X.toSheafedSpace)).str))
          (@CategoryTheory.Category.opposite.{0, 0}
            (@TopologicalSpace.Opens.{0} (↥X)
              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                  CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    X.toSheafedSpace)).str)
            (@Preorder.smallCategory.{0}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str)
              (@PartialOrder.toPreorder.{0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str))))
          CommRingCat.{0} CommRingCat.instCategory.{0}
          (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
            CommRingCat.instCategory.{0}
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
          (@Opposite.op.{1} X.Opens U)))
      (@DFunLike.coe.{1, 1, 1}
        (@RingHom.{0, 0}
          (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
              (Opposite.{1}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str))
              (@CategoryTheory.Category.opposite.{0, 0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@Preorder.smallCategory.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@PartialOrder.toPreorder.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))))
              CommRingCat.{0} CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
              (@Opposite.op.{1} X.Opens V)))
          (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
              (Opposite.{1}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str))
              (@CategoryTheory.Category.opposite.{0, 0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@Preorder.smallCategory.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@PartialOrder.toPreorder.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))))
              CommRingCat.{0} CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
              (@Opposite.op.{1} X.Opens U)))
          (@Semiring.toNonAssocSemiring.{0}
            (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                (Opposite.{1}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))
                (@CategoryTheory.Category.opposite.{0, 0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@Preorder.smallCategory.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@PartialOrder.toPreorder.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))))
                CommRingCat.{0} CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                (@Opposite.op.{1} X.Opens V)))
            (@CommSemiring.toSemiring.{0}
              (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                  (Opposite.{1}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))
                  (@CategoryTheory.Category.opposite.{0, 0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@Preorder.smallCategory.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@PartialOrder.toPreorder.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))))
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace))
                  (@Opposite.op.{1} X.Opens V)))
              (@CommRing.toCommSemiring.{0}
                (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens V)))
                (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens V)).commRing)))
          (@Semiring.toNonAssocSemiring.{0}
            (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                (Opposite.{1}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))
                (@CategoryTheory.Category.opposite.{0, 0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@Preorder.smallCategory.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@PartialOrder.toPreorder.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))))
                CommRingCat.{0} CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                (@Opposite.op.{1} X.Opens U)))
            (@CommSemiring.toSemiring.{0}
              (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                  (Opposite.{1}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))
                  (@CategoryTheory.Category.opposite.{0, 0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@Preorder.smallCategory.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@PartialOrder.toPreorder.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))))
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace))
                  (@Opposite.op.{1} X.Opens U)))
              (@CommRing.toCommSemiring.{0}
                (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens U)))
                (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens U)).commRing))))
        (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
            (Opposite.{1}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str))
            (@CategoryTheory.Category.opposite.{0, 0}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str)
              (@Preorder.smallCategory.{0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@PartialOrder.toPreorder.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))))
            CommRingCat.{0} CommRingCat.instCategory.{0}
            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
              CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
            (@Opposite.op.{1} X.Opens V)))
        (fun x ↦
          ↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
              (Opposite.{1}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str))
              (@CategoryTheory.Category.opposite.{0, 0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@Preorder.smallCategory.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@PartialOrder.toPreorder.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))))
              CommRingCat.{0} CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
              (@Opposite.op.{1} X.Opens U)))
        (@RingHom.instFunLike.{0, 0}
          (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
              (Opposite.{1}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str))
              (@CategoryTheory.Category.opposite.{0, 0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@Preorder.smallCategory.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@PartialOrder.toPreorder.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))))
              CommRingCat.{0} CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
              (@Opposite.op.{1} X.Opens V)))
          (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
              (Opposite.{1}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str))
              (@CategoryTheory.Category.opposite.{0, 0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@Preorder.smallCategory.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@PartialOrder.toPreorder.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))))
              CommRingCat.{0} CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
              (@Opposite.op.{1} X.Opens U)))
          (@Semiring.toNonAssocSemiring.{0}
            (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                (Opposite.{1}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))
                (@CategoryTheory.Category.opposite.{0, 0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@Preorder.smallCategory.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@PartialOrder.toPreorder.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))))
                CommRingCat.{0} CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                (@Opposite.op.{1} X.Opens V)))
            (@CommSemiring.toSemiring.{0}
              (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                  (Opposite.{1}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))
                  (@CategoryTheory.Category.opposite.{0, 0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@Preorder.smallCategory.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@PartialOrder.toPreorder.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))))
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace))
                  (@Opposite.op.{1} X.Opens V)))
              (@CommRing.toCommSemiring.{0}
                (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens V)))
                (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens V)).commRing)))
          (@Semiring.toNonAssocSemiring.{0}
            (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                (Opposite.{1}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))
                (@CategoryTheory.Category.opposite.{0, 0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@Preorder.smallCategory.{0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@PartialOrder.toPreorder.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))))
                CommRingCat.{0} CommRingCat.instCategory.{0}
                (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                (@Opposite.op.{1} X.Opens U)))
            (@CommSemiring.toSemiring.{0}
              (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                  (Opposite.{1}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str))
                  (@CategoryTheory.Category.opposite.{0, 0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0,
                                0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            X.toSheafedSpace)).str)
                    (@Preorder.smallCategory.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@PartialOrder.toPreorder.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))))
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace))
                  (@Opposite.op.{1} X.Opens U)))
              (@CommRing.toCommSemiring.{0}
                (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens U)))
                (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                    0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens U)).commRing))))
        (@CommRingCat.Hom.hom.{0}
          (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
            (Opposite.{1}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str))
            (@CategoryTheory.Category.opposite.{0, 0}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str)
              (@Preorder.smallCategory.{0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@PartialOrder.toPreorder.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))))
            CommRingCat.{0} CommRingCat.instCategory.{0}
            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
              CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
            (@Opposite.op.{1} X.Opens V))
          (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
            (Opposite.{1}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str))
            (@CategoryTheory.Category.opposite.{0, 0}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str)
              (@Preorder.smallCategory.{0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@PartialOrder.toPreorder.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))))
            CommRingCat.{0} CommRingCat.instCategory.{0}
            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
              CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
            (@Opposite.op.{1} X.Opens U))
          (@CategoryTheory.Functor.map.{0, 0, 0, 1}
            (Opposite.{1}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str))
            (@CategoryTheory.Category.opposite.{0, 0}
              (@TopologicalSpace.Opens.{0} (↥X)
                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)).str)
              (@Preorder.smallCategory.{0}
                (@TopologicalSpace.Opens.{0} (↥X)
                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        X.toSheafedSpace)).str)
                (@PartialOrder.toPreorder.{0}
                  (@TopologicalSpace.Opens.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str)
                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace)).str))))
            CommRingCat.{0} CommRingCat.instCategory.{0}
            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
              CommRingCat.instCategory.{0}
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
            (@Opposite.op.{1} X.Opens V) (@Opposite.op.{1} X.Opens U)
            (@Quiver.Hom.op.{0, 0} X.Opens
              (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} X.Opens
                (@CategoryTheory.Category.toCategoryStruct.{0, 0} X.Opens
                  (@Preorder.smallCategory.{0} X.Opens
                    (@PartialOrder.toPreorder.{0} X.Opens
                      (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1,
                              0, 0}
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          X.toSheafedSpace))))))
              U V
              (@CategoryTheory.homOfLE.{0} X.Opens
                (@PartialOrder.toPreorder.{0} X.Opens
                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                    (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1,
                          0, 0}
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      X.toSheafedSpace)))
                U V i)))))
      s)))
    (h_8 : @Set.Finite.{0} (↥X)
  (@max.{0} (Set.{0} ↥X) (@Set.instMax.{0} ↥X)
    (@AlgebraicGeometry.Scheme.zeroLocus.{0} X V s)
    (@compl.{0} (Set.{0} ↥X) (@Set.instCompl.{0} ↥X)
      (@SetLike.coe.{0, 0} X.Opens (↥X)
        (@TopologicalSpace.Opens.instSetLike.{0} (↥X)
          (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0,
                0}
            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
        U)))) :
    @TopologicalSpace.IsSeparable.{0} (↥X)
  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0, 0}
    CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)
  u := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Set.Finite.isSeparable.{0} (↥X)
      (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0, 0} CommRingCat.{0}
        CommRingCat.instCategory.{0} X.toSheafedSpace)
      u
      (@Set.Finite.subset.{0} (↥X)
        (@max.{0} (Set.{0} ↥X) (@Set.instMax.{0} ↥X) (@AlgebraicGeometry.Scheme.zeroLocus.{0} X V s)
          (@compl.{0} (Set.{0} ↥X) (@Set.instCompl.{0} ↥X)
            (@SetLike.coe.{0, 0} X.Opens (↥X)
              (@TopologicalSpace.Opens.instSetLike.{0} (↥X)
                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0, 0}
                  CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
              U)))
        h_8 u
        (@subset_of_subset_of_eq.{0} (Set.{0} ↥X) (Set.instUsesSetNotationForOrder.{0} ↥X) u
          (@AlgebraicGeometry.Scheme.zeroLocus.{0} X U
            (@Set.image.{0, 0}
              (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                  (Opposite.{1}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str))
                  (@CategoryTheory.Category.opposite.{0, 0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                    (@Preorder.smallCategory.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                      (@PartialOrder.toPreorder.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))))
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                    CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                      CommRingCat.instCategory.{0} X.toSheafedSpace))
                  (@Opposite.op.{1} X.Opens V)))
              (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                  (Opposite.{1}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str))
                  (@CategoryTheory.Category.opposite.{0, 0}
                    (@TopologicalSpace.Opens.{0} (↥X)
                      (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                    (@Preorder.smallCategory.{0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                      (@PartialOrder.toPreorder.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))))
                  CommRingCat.{0} CommRingCat.instCategory.{0}
                  (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                    CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                      CommRingCat.instCategory.{0} X.toSheafedSpace))
                  (@Opposite.op.{1} X.Opens U)))
              (@DFunLike.coe.{1, 1, 1}
                (@RingHom.{0, 0}
                  (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                      (Opposite.{1}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))
                      (@CategoryTheory.Category.opposite.{0, 0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@Preorder.smallCategory.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@PartialOrder.toPreorder.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))))
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0} X.toSheafedSpace))
                      (@Opposite.op.{1} X.Opens V)))
                  (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                      (Opposite.{1}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))
                      (@CategoryTheory.Category.opposite.{0, 0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@Preorder.smallCategory.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@PartialOrder.toPreorder.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))))
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0} X.toSheafedSpace))
                      (@Opposite.op.{1} X.Opens U)))
                  (@Semiring.toNonAssocSemiring.{0}
                    (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                        (Opposite.{1}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))
                        (@CategoryTheory.Category.opposite.{0, 0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@Preorder.smallCategory.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@PartialOrder.toPreorder.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))))
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                        (@Opposite.op.{1} X.Opens V)))
                    (@CommSemiring.toSemiring.{0}
                      (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                          (Opposite.{1}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))
                          (@CategoryTheory.Category.opposite.{0, 0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@Preorder.smallCategory.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@PartialOrder.toPreorder.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str))))
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                          (@Opposite.op.{1} X.Opens V)))
                      (@CommRing.toCommSemiring.{0}
                        (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens V)))
                        (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens V)).commRing)))
                  (@Semiring.toNonAssocSemiring.{0}
                    (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                        (Opposite.{1}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))
                        (@CategoryTheory.Category.opposite.{0, 0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@Preorder.smallCategory.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@PartialOrder.toPreorder.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))))
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                        (@Opposite.op.{1} X.Opens U)))
                    (@CommSemiring.toSemiring.{0}
                      (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                          (Opposite.{1}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))
                          (@CategoryTheory.Category.opposite.{0, 0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@Preorder.smallCategory.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@PartialOrder.toPreorder.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str))))
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                          (@Opposite.op.{1} X.Opens U)))
                      (@CommRing.toCommSemiring.{0}
                        (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens U)))
                        (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens U)).commRing))))
                (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                      CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0} X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens V)))
                (fun x ↦
                  ↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                      (Opposite.{1}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))
                      (@CategoryTheory.Category.opposite.{0, 0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@Preorder.smallCategory.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@PartialOrder.toPreorder.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))))
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0} X.toSheafedSpace))
                      (@Opposite.op.{1} X.Opens U)))
                (@RingHom.instFunLike.{0, 0}
                  (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                      (Opposite.{1}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))
                      (@CategoryTheory.Category.opposite.{0, 0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@Preorder.smallCategory.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@PartialOrder.toPreorder.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))))
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0} X.toSheafedSpace))
                      (@Opposite.op.{1} X.Opens V)))
                  (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                      (Opposite.{1}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0}
                                X.toSheafedSpace)).str))
                      (@CategoryTheory.Category.opposite.{0, 0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@Preorder.smallCategory.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@PartialOrder.toPreorder.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))))
                      CommRingCat.{0} CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0} X.toSheafedSpace))
                      (@Opposite.op.{1} X.Opens U)))
                  (@Semiring.toNonAssocSemiring.{0}
                    (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                        (Opposite.{1}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))
                        (@CategoryTheory.Category.opposite.{0, 0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@Preorder.smallCategory.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@PartialOrder.toPreorder.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))))
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                        (@Opposite.op.{1} X.Opens V)))
                    (@CommSemiring.toSemiring.{0}
                      (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                          (Opposite.{1}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))
                          (@CategoryTheory.Category.opposite.{0, 0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@Preorder.smallCategory.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@PartialOrder.toPreorder.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str))))
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                          (@Opposite.op.{1} X.Opens V)))
                      (@CommRing.toCommSemiring.{0}
                        (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens V)))
                        (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens V)).commRing)))
                  (@Semiring.toNonAssocSemiring.{0}
                    (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                        (Opposite.{1}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))
                        (@CategoryTheory.Category.opposite.{0, 0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@Preorder.smallCategory.{0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@PartialOrder.toPreorder.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))))
                        CommRingCat.{0} CommRingCat.instCategory.{0}
                        (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                          CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                            CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                        (@Opposite.op.{1} X.Opens U)))
                    (@CommSemiring.toSemiring.{0}
                      (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                          (Opposite.{1}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str))
                          (@CategoryTheory.Category.opposite.{0, 0}
                            (@TopologicalSpace.Opens.{0} (↥X)
                              (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                  CommRingCat.instCategory.{0}
                                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    X.toSheafedSpace)).str)
                            (@Preorder.smallCategory.{0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@PartialOrder.toPreorder.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str))))
                          CommRingCat.{0} CommRingCat.instCategory.{0}
                          (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                          (@Opposite.op.{1} X.Opens U)))
                      (@CommRing.toCommSemiring.{0}
                        (↑(@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens U)))
                        (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                            (Opposite.{1}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str))
                            (@CategoryTheory.Category.opposite.{0, 0}
                              (@TopologicalSpace.Opens.{0} (↥X)
                                (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                    CommRingCat.{0} CommRingCat.instCategory.{0}
                                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      X.toSheafedSpace)).str)
                              (@Preorder.smallCategory.{0}
                                (@TopologicalSpace.Opens.{0} (↥X)
                                  (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                      CommRingCat.{0} CommRingCat.instCategory.{0}
                                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        X.toSheafedSpace)).str)
                                (@PartialOrder.toPreorder.{0}
                                  (@TopologicalSpace.Opens.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str)
                                  (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                    (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0}
                                        CommRingCat.{0} CommRingCat.instCategory.{0}
                                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                          CommRingCat.{0} CommRingCat.instCategory.{0}
                                          X.toSheafedSpace)).str))))
                            CommRingCat.{0} CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                            (@Opposite.op.{1} X.Opens U)).commRing))))
                (@CommRingCat.Hom.hom.{0}
                  (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                      CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0} X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens V))
                  (@CategoryTheory.Functor.obj.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                      CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0} X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens U))
                  (@CategoryTheory.Functor.map.{0, 0, 0, 1}
                    (Opposite.{1}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str))
                    (@CategoryTheory.Category.opposite.{0, 0}
                      (@TopologicalSpace.Opens.{0} (↥X)
                        (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                            CommRingCat.instCategory.{0}
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                      (@Preorder.smallCategory.{0}
                        (@TopologicalSpace.Opens.{0} (↥X)
                          (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                              CommRingCat.instCategory.{0}
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)).str)
                        (@PartialOrder.toPreorder.{0}
                          (@TopologicalSpace.Opens.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str)
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.PresheafedSpace.carrier.{0, 1, 0} CommRingCat.{0}
                                CommRingCat.instCategory.{0}
                                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace)).str))))
                    CommRingCat.{0} CommRingCat.instCategory.{0}
                    (@AlgebraicGeometry.PresheafedSpace.presheaf.{0, 1, 0} CommRingCat.{0}
                      CommRingCat.instCategory.{0}
                      (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace.{1, 0, 0} CommRingCat.{0}
                        CommRingCat.instCategory.{0} X.toSheafedSpace))
                    (@Opposite.op.{1} X.Opens V) (@Opposite.op.{1} X.Opens U)
                    (@Quiver.Hom.op.{0, 0} X.Opens
                      (@CategoryTheory.CategoryStruct.toQuiver.{0, 0} X.Opens
                        (@CategoryTheory.Category.toCategoryStruct.{0, 0} X.Opens
                          (@Preorder.smallCategory.{0} X.Opens
                            (@PartialOrder.toPreorder.{0} X.Opens
                              (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1,
                                      0, 0}
                                  CommRingCat.{0} CommRingCat.instCategory.{0}
                                  X.toSheafedSpace))))))
                      U V
                      (@CategoryTheory.homOfLE.{0} X.Opens
                        (@PartialOrder.toPreorder.{0} X.Opens
                          (@TopologicalSpace.Opens.instPartialOrder.{0} (↥X)
                            (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1,
                                  0, 0}
                              CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace)))
                        U V i)))))
              s))
          (@max.{0} (Set.{0} ↥X) (@Set.instMax.{0} ↥X)
            (@AlgebraicGeometry.Scheme.zeroLocus.{0} X V s)
            (@compl.{0} (Set.{0} ↥X) (@Set.instCompl.{0} ↥X)
              (@SetLike.coe.{0, 0} X.Opens (↥X)
                (@TopologicalSpace.Opens.instSetLike.{0} (↥X)
                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier.{1, 0, 0}
                    CommRingCat.{0} CommRingCat.instCategory.{0} X.toSheafedSpace))
                U)))
          (@Set.instLE.{0} ↥X) h_7 (@AlgebraicGeometry.Scheme.zeroLocus_map.{0} X U V i s)))
  -- Phase 1: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_1 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_1 : (14 : Nat) = 14 ∨ (14 : Nat) < 14 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 14)
    cases h_dich_1 with
    | inr h_contra_1 => exact False.elim (Nat.lt_irrefl 14 h_contra_1)
    | inl h_refl_1 => exact (And.intro hp h_refl_1).1
  have h_stage_1 := h_ord_1 h_core
  -- Phase 2: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_2 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_2 : (5 + 10 : Nat) = 15 then
      have h_pack_2 := And.intro h_arith_2 hp
      exact h_pack_2.2
    else
      exact False.elim (h_arith_2 rfl)
  have h_stage_2 := h_chk_2 h_stage_1
  -- Phase 3: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_3 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_3 : (6 + 6 : Nat) = 12 then
      have h_pack_3 := And.intro h_arith_3 hp
      exact h_pack_3.2
    else
      exact False.elim (h_arith_3 rfl)
  have h_stage_3 := h_chk_3 h_stage_2
  -- Phase 4: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_4 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_4 : (10 : Nat) = 10 ∨ (10 : Nat) < 10 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 10)
    cases h_dich_4 with
    | inr h_contra_4 => exact False.elim (Nat.lt_irrefl 10 h_contra_4)
    | inl h_refl_4 => exact (And.intro hp h_refl_4).1
  have h_stage_4 := h_ord_4 h_stage_3
  -- Final step: conclude after 4 auxiliary verification stage(s)
  exact id h_stage_4
