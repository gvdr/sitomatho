import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.SuccPred.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Order.le_of_lt_succ (Order)
-- Step 1: Order.succ_le_succ (Order)
-- Step 3: sup_of_le_left (sup_of_le_left)
theorem akcm_2026_0002
    {α : Type}
    [inst_2 : LinearOrder α]
    [inst_3 : SuccOrder α]
    {a : α}
    {b : α}
    (h_6 : a < Order.succ b) :
    max (Order.succ b) (Order.succ a) = Order.succ b :=
  @sup_of_le_left.{0} α
  (@Lattice.toSemilatticeSup.{0} α
    (@DistribLattice.toLattice.{0} α (@instDistribLatticeOfLinearOrder.{0} α inst_2)))
  (@Order.succ.{0} α
    (@PartialOrder.toPreorder.{0} α
      (@SemilatticeInf.toPartialOrder.{0} α
        (@Lattice.toSemilatticeInf.{0} α
          (@DistribLattice.toLattice.{0} α (@instDistribLatticeOfLinearOrder.{0} α inst_2)))))
    inst_3 b)
  (@Order.succ.{0} α
    (@PartialOrder.toPreorder.{0} α
      (@SemilatticeInf.toPartialOrder.{0} α
        (@Lattice.toSemilatticeInf.{0} α
          (@DistribLattice.toLattice.{0} α (@instDistribLatticeOfLinearOrder.{0} α inst_2)))))
    inst_3 a)
  (@Order.succ_le_succ.{0} α
    (@PartialOrder.toPreorder.{0} α
      (@SemilatticeInf.toPartialOrder.{0} α
        (@Lattice.toSemilatticeInf.{0} α
          (@DistribLattice.toLattice.{0} α (@instDistribLatticeOfLinearOrder.{0} α inst_2)))))
    inst_3 a b (@Order.le_of_lt_succ.{0} α inst_2 inst_3 a b h_6))
