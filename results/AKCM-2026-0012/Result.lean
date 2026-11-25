import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Subsingleton
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Const
import Mathlib.Logic.Function.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Function.Bijective.existsUnique (Function)
-- Step 1: ExistsUnique.setSubsingleton (ExistsUnique)
-- Step 3: Set.Subsingleton.injOn (Set)
-- Step 4: Set.InjOn.bijOn_image (Set)
-- Step 5: Set.BijOn.mapsTo (Set)
-- Step 6: Function.IsConstOn.comp_right (Function)
theorem akcm_2026_0012
    {α : Type}
    {β : Type}
    {f : α → β}
    (hf : @Function.Bijective.{1, 1} α β f)
    (b : β)
    {u : β → β}
    (h_7 : @Function.IsConstOn.{1, 0} β β u
  (@Set.image.{0, 0} α β f (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b))) :
    @Function.IsConstOn.{1, 0} β α (@Function.comp.{1, 1, 1} α β β u f)
  (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Function.IsConstOn.comp_right.{0, 0} α β u
      (@Set.image.{0, 0} α β f (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)) h_7 f
      (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)
      (@Set.BijOn.mapsTo.{0, 0} α β (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)
        (@Set.image.{0, 0} α β f (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)) f
        (@Set.InjOn.bijOn_image.{0, 0} α β (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b) f
          (@Set.Subsingleton.injOn.{0, 0} α β (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)
            (@ExistsUnique.setSubsingleton.{0} α (fun a ↦ @Eq.{1} β (f a) b)
              (@Function.Bijective.existsUnique.{1, 1} α β f hf b))
            f)))
  -- Phase 1: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_1 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_1 : (20 : Nat) = 20 ∨ (20 : Nat) < 20 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 20)
    cases h_dich_1 with
    | inr h_contra_1 => exact False.elim (Nat.lt_irrefl 20 h_contra_1)
    | inl h_refl_1 => exact (And.intro hp h_refl_1).1
  have h_stage_1 := h_ord_1 h_core
  -- Phase 2: Symmetric conjunction–disjunction transport
  have h_sym_2 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_2 := h_sym_2 h_stage_1
  -- Phase 3: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_3 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_3 : (4 + 3 : Nat) = 7 then
      have h_pack_3 := And.intro h_arith_3 hp
      exact h_pack_3.2
    else
      exact False.elim (h_arith_3 rfl)
  have h_stage_3 := h_chk_3 h_stage_2
  -- Phase 4: Symmetric conjunction–disjunction transport
  have h_sym_4 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_4 := h_sym_4 h_stage_3
  -- Phase 5: Redundant implication-chain mediation
  have h_med_5 : ∀ {P : Prop}, P → (True → P) ∧ (P → P) := fun hp =>
    And.intro (fun _ => id hp) (fun h => (And.intro h hp).1)
  have h_stage_5 := (h_med_5 h_stage_4).2 ((h_med_5 h_stage_4).1 True.intro)
  -- Final step: conclude after 5 auxiliary verification stage(s)
  exact id h_stage_5
