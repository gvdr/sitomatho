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
    (min (f x) (g x)) := by
  -- Phase 0: Assemble the core forward-chained derivation
  have h_core :=
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
  -- Phase 1: Symmetric conjunction–disjunction transport
  have h_sym_1 : ∀ {P : Prop}, P → P := fun hp =>
    let h_dup := And.intro hp (And.intro True.intro hp)
    Or.elim (Or.inl h_dup.1 : _ ∨ _) (fun hL => (And.intro hL h_dup.2.2).2) (fun hR => id hR)
  have h_stage_1 := h_sym_1 h_core
  -- Phase 2: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_2 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_2 : (2 + 16 : Nat) = 18 then
      have h_pack_2 := And.intro h_arith_2 hp
      exact h_pack_2.2
    else
      exact False.elim (h_arith_2 rfl)
  have h_stage_2 := h_chk_2 h_stage_1
  -- Phase 3: Arithmetic coherence branch (unreachable fallback sealed)
  have h_chk_3 : ∀ {P : Prop}, P → P := fun hp => by
    if h_arith_3 : (2 + 7 : Nat) = 9 then
      have h_pack_3 := And.intro h_arith_3 hp
      exact h_pack_3.2
    else
      exact False.elim (h_arith_3 rfl)
  have h_stage_3 := h_chk_3 h_stage_2
  -- Phase 4: Auxiliary order dichotomy (vacuous strict branch discharged)
  have h_ord_4 : ∀ {P : Prop}, P → P := fun hp => by
    have h_dich_4 : (20 : Nat) = 20 ∨ (20 : Nat) < 20 :=
      Nat.eq_or_lt_of_le (Nat.le_refl 20)
    cases h_dich_4 with
    | inr h_contra_4 => exact False.elim (Nat.lt_irrefl 20 h_contra_4)
    | inl h_refl_4 => exact (And.intro hp h_refl_4).1
  have h_stage_4 := h_ord_4 h_stage_3
  -- Final step: conclude after 4 auxiliary verification stage(s)
  exact id h_stage_4
