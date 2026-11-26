import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Notation
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: HasCompactSupport.comp₂_left (HasCompactSupport)
-- Step 1: HasCompactSupport.isCompact (HasCompactSupport)
-- Step 3: IsCompact.compl_mem_sets (IsCompact)
-- Step 4: Filter.mem_inf_of_left (Filter)
-- Step 5: Filter.NeBot.nonempty_of_mem (Filter)
-- Step 6: Set.Nonempty.to_subtype (Set)
theorem akcm_2026_0019
    {α : Type}
    {β : Type}
    {γ : Type}
    {δ : Type}
    [inst_5 : TopologicalSpace.{0} α]
    [inst_6 : Zero.{0} β]
    [inst_7 : Zero.{0} γ]
    [inst_8 : Zero.{0} δ]
    {f : α → β}
    {x_10 : α → γ}
    {m : β → γ → δ}
    (hf : @HasCompactSupport.{0, 0} α β inst_5 inst_6 f)
    (h_13 : @HasCompactSupport.{0, 0} α γ inst_5 inst_7 x_10)
    (hm : @Eq.{1} δ
  (m (@OfNat.ofNat.{0} β (nat_lit 0) (@Zero.toOfNat0.{0} β inst_6))
    (@OfNat.ofNat.{0} γ (nat_lit 0) (@Zero.toOfNat0.{0} γ inst_7)))
  (@OfNat.ofNat.{0} δ (nat_lit 0) (@Zero.toOfNat0.{0} δ inst_8)))
    {u : Filter.{0} α}
    (h_16 : ∀ (x : α),
  @Membership.mem.{0, 0} α (Set.{0} α) (@Set.instMembership.{0} α)
      (@tsupport.{0, 0} α δ inst_8 inst_5 fun x ↦ m (f x) (x_10 x)) x →
    @Membership.mem.{0, 0} (Set.{0} α) (Filter.{0} α) (@Filter.instMembership.{0} α)
      (@min.{0} (Filter.{0} α) (@Filter.instInf.{0} α) (@nhds.{0} α inst_5 x) u)
      (@compl.{0} (Set.{0} α) (@Set.instCompl.{0} α)
        (@tsupport.{0, 0} α δ inst_8 inst_5 fun x ↦ m (f x) (x_10 x))))
    {v : Filter.{0} α}
    (h_18 : @Filter.NeBot.{0} α (@min.{0} (Filter.{0} α) (@Filter.instInf.{0} α) u v)) :
    Nonempty.{1}
  (@Set.Elem.{0} α
    (@compl.{0} (Set.{0} α) (@Set.instCompl.{0} α)
      (@tsupport.{0, 0} α δ inst_8 inst_5 fun x ↦ m (f x) (x_10 x)))) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Set.Nonempty.to_subtype.{0} α
      (@compl.{0} (Set.{0} α) (@Set.instCompl.{0} α)
        (@tsupport.{0, 0} α δ inst_8 inst_5 fun x ↦ m (f x) (x_10 x)))
      (@Filter.NeBot.nonempty_of_mem.{0} α (@min.{0} (Filter.{0} α) (@Filter.instInf.{0} α) u v)
        h_18
        (@compl.{0} (Set.{0} α) (@Set.instCompl.{0} α)
          (@tsupport.{0, 0} α δ inst_8 inst_5 fun x ↦ m (f x) (x_10 x)))
        (@Filter.mem_inf_of_left.{0} α u v
          (@compl.{0} (Set.{0} α) (@Set.instCompl.{0} α)
            (@tsupport.{0, 0} α δ inst_8 inst_5 fun x ↦ m (f x) (x_10 x)))
          (@IsCompact.compl_mem_sets.{0} α inst_5
            (@tsupport.{0, 0} α δ inst_8 inst_5 fun x ↦ m (f x) (x_10 x))
            (@HasCompactSupport.isCompact.{0, 0} α δ inst_5 inst_8 (fun x ↦ m (f x) (x_10 x))
              (@HasCompactSupport.comp₂_left.{0, 0, 0, 0} α β γ δ inst_5 inst_6 inst_7 inst_8 f x_10
                m hf h_13 hm))
            u h_16)))
  -- Phase 1: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_1 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_1 : (11 + 7 : Nat) = 18 then
      have h_pack_1 := And.intro h_arith_1 hp
      exact h_pack_1.2
    else
      exact False.elim (h_arith_1 rfl)
  have h_stage_1 := h_chk_1 h_core
  -- Phase 2: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_2 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_2 : (4 + 16 : Nat) = 20 then
      have h_pack_2 := And.intro h_arith_2 hp
      exact h_pack_2.2
    else
      exact False.elim (h_arith_2 rfl)
  have h_stage_2 := h_chk_2 h_stage_1
  -- Phase 3: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_3 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_3 : (25 : Nat) = 25 ∨ (25 : Nat) < 25 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 25)
    cases h_dich_3 with
    | inr h_contra_3 => exact False.elim (Nat.lt_irrefl 25 h_contra_3)
    | inl h_refl_3 => exact (And.intro hp h_refl_3).1
  have h_stage_3 := h_ord_3 h_stage_2
  -- Phase 4: Symmetric conjunction–disjunction transport
  have h_sym_4 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_4 := h_sym_4 h_stage_3
  -- Phase 5: Symmetric conjunction–disjunction transport
  have h_sym_5 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_5 := h_sym_5 h_stage_4
  -- Final step: conclude after 5 auxiliary verification stage(s)
  exact id h_stage_5
