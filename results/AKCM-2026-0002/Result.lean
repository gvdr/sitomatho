import Mathlib.Basic.Denumerable
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.Basic
import Mathlib.Data.PFun

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Primrec.primrecPred (Primrec)
-- Step 1: PrimrecPred.not (PrimrecPred)
-- Step 2: PrimrecPred.decide (PrimrecPred)
-- Step 3: Primrec.nat_rec (Primrec)
-- Step 4: Primrec₂.to_comp (Primrec₂)
-- Step 6: Computable₂.partrec₂ (Computable₂)
-- Step 8: Partrec.rfind (Partrec)
theorem akcm_2026_0002
    {α : Type}
    [inst_2 : Primcodable.{0} α]
    {p : α → Prop}
    [inst_4 : @DecidablePred.{1} α p]
    (hp : @Primrec.{0, 0} α Bool inst_2 Primcodable.bool fun a ↦ @decide (p a) (inst_4 a))
    {u : α → Prod.{0, 0} Nat Bool → Bool}
    (h_7 : @Primrec₂.{0, 0, 0} α (Prod.{0, 0} Nat Bool) Bool inst_2
  (@Primcodable.prod.{0, 0} Nat Bool
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool)
  Primcodable.bool u) :
    @Partrec.{0, 0} α Nat inst_2 (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat)
  fun a ↦
  Nat.rfind
    (@PFun.lift.{0, 0} Nat Bool fun n ↦
      @Nat.rec.{1} (fun x ↦ Bool)
        (@decide (Not (p a)) (@instDecidableNot (p a) (inst_4 a)))
        (fun n IH ↦ u a (@Prod.mk.{0, 0} Nat Bool n IH)) n) :=   @Partrec.rfind.{0} α inst_2
  (fun a ↦
    @PFun.lift.{0, 0} Nat Bool fun n ↦
      @Nat.rec.{1} (fun x ↦ Bool) (@decide (Not (p a)) (@instDecidableNot (p a) (inst_4 a)))
        (fun n IH ↦ u a (@Prod.mk.{0, 0} Nat Bool n IH)) n)
  (@Computable₂.partrec₂.{0, 0, 0} α Nat Bool inst_2
    (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool
    (fun a n ↦
      @Nat.rec.{1} (fun x ↦ Bool) (@decide (Not (p a)) (@instDecidableNot (p a) (inst_4 a)))
        (fun n IH ↦ u a (@Prod.mk.{0, 0} Nat Bool n IH)) n)
    (@Primrec₂.to_comp.{0, 0, 0} α Nat Bool inst_2
      (@Primcodable.ofDenumerable.{0} Nat Denumerable.nat) Primcodable.bool
      (fun a n ↦
        @Nat.rec.{1} (fun x ↦ Bool) (@decide (Not (p a)) (@instDecidableNot (p a) (inst_4 a)))
          (fun n IH ↦ u a (@Prod.mk.{0, 0} Nat Bool n IH)) n)
      (@Primrec.nat_rec.{0, 0} α Bool inst_2 Primcodable.bool
        (fun a ↦ @decide (Not (p a)) (@instDecidableNot (p a) (inst_4 a))) u
        (@PrimrecPred.decide.{0} α inst_2 (fun a ↦ Not (p a))
          (fun a ↦ @instDecidableNot (p a) (inst_4 a))
          (@PrimrecPred.not.{0} α inst_2 p (@Primrec.primrecPred.{0} α inst_2 p inst_4 hp)))
        h_7)))
