import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Order.SetNotation
import Mathlib.Topology.Clopen
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Defs.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Set.Finite.isClopen_biInter (Set)
-- Step 1: IsClopen.union (IsClopen)
-- Step 2: IsClopen.biUnion_connectedComponent_eq (IsClopen)
theorem akcm_2026_0006
    {X : Type}
    [inst_2 : TopologicalSpace X]
    {Y : Type}
    {s : Set Y}
    (hs : s.Finite)
    {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen (f i)) :
    ⋃ x ∈ (⋂ i ∈ s, f i) ∪ ⋂ i ∈ s, f i, connectedComponent x =
  (⋂ i ∈ s, f i) ∪ ⋂ i ∈ s, f i :=
  @IsClopen.biUnion_connectedComponent_eq.{0} X inst_2
  (@max.{0} (Set.{0} X) (@Set.instMax.{0} X)
    (⋂ i, ⋂ (_ : @Membership.mem.{0, 0} Y (Set.{0} Y) (@Set.instMembership.{0} Y) s i), f i)
    (⋂ i, ⋂ (_ : @Membership.mem.{0, 0} Y (Set.{0} Y) (@Set.instMembership.{0} Y) s i), f i))
  (@IsClopen.union.{0} X inst_2
    (⋂ i, ⋂ (_ : @Membership.mem.{0, 0} Y (Set.{0} Y) (@Set.instMembership.{0} Y) s i), f i)
    (⋂ i, ⋂ (_ : @Membership.mem.{0, 0} Y (Set.{0} Y) (@Set.instMembership.{0} Y) s i), f i)
    (@Set.Finite.isClopen_biInter.{0, 0} X inst_2 Y s hs f h)
    (@Set.Finite.isClopen_biInter.{0, 0} X inst_2 Y s hs f h))
