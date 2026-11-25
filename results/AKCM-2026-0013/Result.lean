import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Subsingleton
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Const
import Mathlib.Logic.Function.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Function.Bijective.existsUnique (Function)
-- Step 2: ExistsUnique.setSubsingleton (ExistsUnique)
-- Step 3: Set.Subsingleton.injOn (Set)
-- Step 5: Set.InjOn.bijOn_image (Set)
-- Step 6: Set.BijOn.mapsTo (Set)
-- Step 7: Function.IsConstOn.comp_right (Function)
-- Step 8: Function.IsConstOn.of_eqOn (Function)
theorem akcm_2026_0013
    {α : Type}
    {β : Type}
    {f : α → β}
    (hf : @Function.Bijective.{1, 1} α β f)
    (b : β)
    {u : β → β}
    (h_7 : @Function.IsConstOn.{1, 0} β β u
  (@Set.image.{0, 0} α β f (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)))
    {v : α → β}
    (h_9 : @Set.EqOn.{0, 0} α β (@Function.comp.{1, 1, 1} α β β u f) v
  (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)) :
    @Function.IsConstOn.{1, 0} β α v (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
    @Function.IsConstOn.of_eqOn.{0, 0} α β (@Function.comp.{1, 1, 1} α β β u f) v
      (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)
      (@Function.IsConstOn.comp_right.{0, 0} α β u
        (@Set.image.{0, 0} α β f (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)) h_7 f
        (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)
        (@Set.BijOn.mapsTo.{0, 0} α β (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)
          (@Set.image.{0, 0} α β f (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)) f
          (@Set.InjOn.bijOn_image.{0, 0} α β (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b) f
            (@Set.Subsingleton.injOn.{0, 0} α β (@Set.ofPred.{0} α fun x ↦ @Eq.{1} β (f x) b)
              (@ExistsUnique.setSubsingleton.{0} α (fun a ↦ @Eq.{1} β (f a) b)
                (@Function.Bijective.existsUnique.{1, 1} α β f hf b))
              f))))
      h_9
  -- Phase 1: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_1 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_1 : (18 : Nat) = 18 ∨ (18 : Nat) < 18 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 18)
    cases h_dich_1 with
    | inr h_contra_1 => exact False.elim (Nat.lt_irrefl 18 h_contra_1)
    | inl h_refl_1 => exact (And.intro hp h_refl_1).1
  have h_stage_1 := h_ord_1 h_core
  -- Phase 2: Inductive case-analysis ceremony on a trivial index
  have h_lift_2 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_2 := h_lift_2 h_stage_1 0 rfl
  -- Phase 3: Inductive case-analysis ceremony on a trivial index
  have h_lift_3 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_3 := h_lift_3 h_stage_2 0 rfl
  -- Phase 4: Redundant implication-chain mediation
  have h_med_4 : ∀ {P : Prop}, P → (True → P) ∧ (P → P) := fun hp =>
    And.intro (fun _ => id hp) (fun h => (And.intro h hp).1)
  have h_stage_4 := (h_med_4 h_stage_3).2 ((h_med_4 h_stage_3).1 True.intro)
  -- Phase 5: Inductive case-analysis ceremony on a trivial index
  have h_lift_5 : ∀ {P : Prop}, P → ∀ n : Nat, n = 0 → P := fun hp n hn =>
    match n, hn with
    | 0, _ => (And.intro hp True.intro).1
    | Nat.succ _, h_ne => False.elim (Nat.noConfusion h_ne)
  have h_stage_5 := h_lift_5 h_stage_4 0 rfl
  -- Final step: conclude after 5 auxiliary verification stage(s)
  exact id h_stage_5
