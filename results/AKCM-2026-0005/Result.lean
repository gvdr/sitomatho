import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Antitone.min (Antitone)
-- Step 1: Antitone.max (Antitone)
-- Step 2: Antitone.min (Antitone)
-- Step 3: Antitone.max (Antitone)
theorem akcm_2026_0005
    {α : Type}
    {β : Type}
    [inst_3 : Preorder α]
    [inst_4 : LinearOrder β]
    {f : α → β}
    {g : α → β}
    (hf : Antitone f)
    (hg : Antitone g) :
    Antitone fun x ↦
  max (min (max (min (f x) (g x)) (min (f x) (g x))) (min (f x) (g x)))
    (min (f x) (g x)) :=
  @Antitone.max.{0, 0} α β inst_3 inst_4
  (fun x ↦
    @min.{0} β
      (@SemilatticeInf.toMin.{0} β
        (@Lattice.toSemilatticeInf.{0} β
          (@DistribLattice.toLattice.{0} β (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
      (@max.{0} β
        (@SemilatticeSup.toMax.{0} β
          (@Lattice.toSemilatticeSup.{0} β
            (@DistribLattice.toLattice.{0} β (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
        (@min.{0} β
          (@SemilatticeInf.toMin.{0} β
            (@Lattice.toSemilatticeInf.{0} β
              (@DistribLattice.toLattice.{0} β
                (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
          (f x) (g x))
        (@min.{0} β
          (@SemilatticeInf.toMin.{0} β
            (@Lattice.toSemilatticeInf.{0} β
              (@DistribLattice.toLattice.{0} β
                (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
          (f x) (g x)))
      (@min.{0} β
        (@SemilatticeInf.toMin.{0} β
          (@Lattice.toSemilatticeInf.{0} β
            (@DistribLattice.toLattice.{0} β (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
        (f x) (g x)))
  (fun x ↦
    @min.{0} β
      (@SemilatticeInf.toMin.{0} β
        (@Lattice.toSemilatticeInf.{0} β
          (@DistribLattice.toLattice.{0} β (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
      (f x) (g x))
  (@Antitone.min.{0, 0} α β inst_3 inst_4
    (fun x ↦
      @max.{0} β
        (@SemilatticeSup.toMax.{0} β
          (@Lattice.toSemilatticeSup.{0} β
            (@DistribLattice.toLattice.{0} β (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
        (@min.{0} β
          (@SemilatticeInf.toMin.{0} β
            (@Lattice.toSemilatticeInf.{0} β
              (@DistribLattice.toLattice.{0} β
                (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
          (f x) (g x))
        (@min.{0} β
          (@SemilatticeInf.toMin.{0} β
            (@Lattice.toSemilatticeInf.{0} β
              (@DistribLattice.toLattice.{0} β
                (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
          (f x) (g x)))
    (fun x ↦
      @min.{0} β
        (@SemilatticeInf.toMin.{0} β
          (@Lattice.toSemilatticeInf.{0} β
            (@DistribLattice.toLattice.{0} β (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
        (f x) (g x))
    (@Antitone.max.{0, 0} α β inst_3 inst_4
      (fun x ↦
        @min.{0} β
          (@SemilatticeInf.toMin.{0} β
            (@Lattice.toSemilatticeInf.{0} β
              (@DistribLattice.toLattice.{0} β
                (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
          (f x) (g x))
      (fun x ↦
        @min.{0} β
          (@SemilatticeInf.toMin.{0} β
            (@Lattice.toSemilatticeInf.{0} β
              (@DistribLattice.toLattice.{0} β
                (@instDistribLatticeOfLinearOrder.{0} β inst_4))))
          (f x) (g x))
      (@Antitone.min.{0, 0} α β inst_3 inst_4 f g hf hg)
      (@Antitone.min.{0, 0} α β inst_3 inst_4 f g hf hg))
    (@Antitone.min.{0, 0} α β inst_3 inst_4 f g hf hg))
  (@Antitone.min.{0, 0} α β inst_3 inst_4 f g hf hg)
