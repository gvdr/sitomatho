import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Operations
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.RelClasses

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Filter.tendsto_inf_left (Filter)
-- Step 2: Filter.Tendsto.map_mapsTo_Iic (Filter)
-- Step 4: Set.MapsTo.subset_preimage (Set)
-- Step 5: Set.ssubset_of_ssubset_of_subset (Set)
-- Step 6: ssubset_asymm (ssubset_asymm)
-- Step 7: Set.Ioc_eq_empty (Set)
theorem akcm_2026_0016
    {α : Type}
    {β : Type}
    {f : α → β}
    {x_4 : Filter.{0} α}
    {x_5 : Filter.{0} α}
    {y : Filter.{0} β}
    (h : @Filter.Tendsto.{0, 0} α β f x_4 y)
    {u : Set.{0} (Filter.{0} α)}
    (h_9 : @LT.lt.{0} (Set.{0} (Filter.{0} α))
  (@Preorder.toLT.{0} (Set.{0} (Filter.{0} α))
    (@PartialOrder.toPreorder.{0} (Set.{0} (Filter.{0} α))
      (@SemilatticeInf.toPartialOrder.{0} (Set.{0} (Filter.{0} α))
        (@Lattice.toSemilatticeInf.{0} (Set.{0} (Filter.{0} α))
          (@DistribLattice.toLattice.{0} (Set.{0} (Filter.{0} α))
            (@Set.instDistribLattice.{0} (Filter.{0} α)))))))
  u
  (@Set.Iic.{0} (Filter.{0} α)
    (@PartialOrder.toPreorder.{0} (Filter.{0} α) (@Filter.instPartialOrder.{0} α))
    (@min.{0} (Filter.{0} α) (@Filter.instInf.{0} α) x_4 x_5))) :
    @Eq.{1} (Set.{0} (Set.{0} (Filter.{0} α)))
  (@Set.Ioc.{0} (Set.{0} (Filter.{0} α))
    (@PartialOrder.toPreorder.{0} (Set.{0} (Filter.{0} α))
      (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} (Filter.{0} α))
        (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} (Filter.{0} α))
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Filter.{0} α))
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0}
              (Set.{0} (Filter.{0} α))
              (@Set.instCompleteAtomicBooleanAlgebra.{0} (Filter.{0} α)))))))
    (@Set.preimage.{0, 0} (Filter.{0} α) (Filter.{0} β) (@Filter.map.{0, 0} α β f)
      (@Set.Iic.{0} (Filter.{0} β)
        (@PartialOrder.toPreorder.{0} (Filter.{0} β) (@Filter.instPartialOrder.{0} β))
        y))
    u)
  (@EmptyCollection.emptyCollection.{0} (Set.{0} (Set.{0} (Filter.{0} α)))
    (@Set.instEmptyCollection.{0} (Set.{0} (Filter.{0} α)))) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Set.Ioc_eq_empty.{0} (Set.{0} (Filter.{0} α))
      (@PartialOrder.toPreorder.{0} (Set.{0} (Filter.{0} α))
        (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} (Filter.{0} α))
          (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} (Filter.{0} α))
            (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Filter.{0} α))
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Filter.{0} α))
                (@Set.instCompleteAtomicBooleanAlgebra.{0} (Filter.{0} α)))))))
      u
      (@Set.preimage.{0, 0} (Filter.{0} α) (Filter.{0} β) (@Filter.map.{0, 0} α β f)
        (@Set.Iic.{0} (Filter.{0} β)
          (@PartialOrder.toPreorder.{0} (Filter.{0} β) (@Filter.instPartialOrder.{0} β)) y))
      (@ssubset_asymm.{0} (Set.{0} (Filter.{0} α))
        (Set.instUsesSetNotationForOrder.{0} (Filter.{0} α))
        (@PartialOrder.toPreorder.{0} (Set.{0} (Filter.{0} α))
          (@CompleteSemilatticeInf.toPartialOrder.{0} (Set.{0} (Filter.{0} α))
            (@CompleteLattice.toCompleteSemilatticeInf.{0} (Set.{0} (Filter.{0} α))
              (@CompleteBooleanAlgebra.toCompleteLattice.{0} (Set.{0} (Filter.{0} α))
                (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra.{0} (Set.{0} (Filter.{0} α))
                  (@Set.instCompleteAtomicBooleanAlgebra.{0} (Filter.{0} α)))))))
        u
        (@Set.preimage.{0, 0} (Filter.{0} α) (Filter.{0} β) (@Filter.map.{0, 0} α β f)
          (@Set.Iic.{0} (Filter.{0} β)
            (@PartialOrder.toPreorder.{0} (Filter.{0} β) (@Filter.instPartialOrder.{0} β)) y))
        (@Set.ssubset_of_ssubset_of_subset.{0} (Filter.{0} α) u
          (@Set.Iic.{0} (Filter.{0} α)
            (@PartialOrder.toPreorder.{0} (Filter.{0} α) (@Filter.instPartialOrder.{0} α))
            (@min.{0} (Filter.{0} α) (@Filter.instInf.{0} α) x_4 x_5))
          (@Set.preimage.{0, 0} (Filter.{0} α) (Filter.{0} β) (@Filter.map.{0, 0} α β f)
            (@Set.Iic.{0} (Filter.{0} β)
              (@PartialOrder.toPreorder.{0} (Filter.{0} β) (@Filter.instPartialOrder.{0} β)) y))
          h_9
          (@Set.MapsTo.subset_preimage.{0, 0} (Filter.{0} α) (Filter.{0} β)
            (@Set.Iic.{0} (Filter.{0} α)
              (@PartialOrder.toPreorder.{0} (Filter.{0} α) (@Filter.instPartialOrder.{0} α))
              (@min.{0} (Filter.{0} α) (@Filter.instInf.{0} α) x_4 x_5))
            (@Set.Iic.{0} (Filter.{0} β)
              (@PartialOrder.toPreorder.{0} (Filter.{0} β) (@Filter.instPartialOrder.{0} β)) y)
            (@Filter.map.{0, 0} α β f)
            (@Filter.Tendsto.map_mapsTo_Iic.{0, 0} α β
              (@min.{0} (Filter.{0} α) (@Filter.instInf.{0} α) x_4 x_5) y f
              (@Filter.tendsto_inf_left.{0, 0} α β f x_4 x_5 y h)))))
  -- Phase 1: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_1 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_1 : (6 + 5 : Nat) = 11 then
      have h_pack_1 := And.intro h_arith_1 hp
      exact h_pack_1.2
    else
      exact False.elim (h_arith_1 rfl)
  have h_stage_1 := h_chk_1 h_core
  -- Phase 2: Symmetric conjunction–disjunction transport
  have h_sym_2 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_2 := h_sym_2 h_stage_1
  -- Phase 3: Symmetric conjunction–disjunction transport
  have h_sym_3 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_3 := h_sym_3 h_stage_2
  -- Final step: conclude after 3 auxiliary verification stage(s)
  exact id h_stage_3
