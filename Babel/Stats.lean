import Lean
import Std.Data.HashMap

namespace Babel

open Lean

/-- Why a lemma application or a finished derivation was dropped. -/
inductive Reject
  | selfReuse | repeatedLemma | paddedFact | sizeCap | noUnifier | heartbeat
  | unresolved | dullConclusion
  | fewSteps | fewConcepts | noFocusSymbol | kernelCheck | badAxioms
  | closedByExact | closedBySimp | closedByAesop | unrenderable | duplicateHash
deriving Inhabited, BEq, Repr

def Reject.key : Reject → String
  | .selfReuse => "self_reuse"
  | .repeatedLemma => "repeated_lemma"
  | .paddedFact => "padded_fact"
  | .sizeCap => "size_cap"
  | .noUnifier => "no_unifier"
  | .heartbeat => "heartbeat"
  | .unresolved => "unresolved"
  | .dullConclusion => "dull_conclusion"
  | .fewSteps => "few_steps"
  | .fewConcepts => "few_concepts"
  | .noFocusSymbol => "no_focus_symbol"
  | .kernelCheck => "kernel_check"
  | .badAxioms => "bad_axioms"
  | .closedByExact => "closed_by_exact"
  | .closedBySimp => "closed_by_simp"
  | .closedByAesop => "closed_by_aesop"
  | .unrenderable => "unrenderable"
  | .duplicateHash => "duplicate_hash"

/-- Timings and counters for one `walk` run. Wall-clock values are reported only;
    no search decision reads them. -/
structure WalkStats where
  phaseMs : Std.HashMap String Nat := {}
  rejects : Std.HashMap String Nat := {}
  attempts : Nat := 0
  applicationsTried : Nat := 0
  applicationsSucceeded : Nat := 0
deriving Inhabited

namespace WalkStats

def bump (s : WalkStats) (r : Reject) : WalkStats :=
  { s with rejects := s.rejects.insert r.key (s.rejects.getD r.key 0 + 1) }

def addMs (s : WalkStats) (phase : String) (ms : Nat) : WalkStats :=
  { s with phaseMs := s.phaseMs.insert phase (s.phaseMs.getD phase 0 + ms) }

/-- The most frequent rejection reason. Ties go to the alphabetically first key. -/
def dominantReject (s : WalkStats) : Option (String × Nat) :=
  s.rejects.fold (init := none) fun best key count =>
    match best with
    | none => some (key, count)
    | some (bestKey, bestCount) =>
        if count > bestCount || (count == bestCount && key < bestKey) then some (key, count)
        else best

private def countsToJson (counts : Std.HashMap String Nat) : Json :=
  let sorted := counts.toList.mergeSort fun a b => a.1 < b.1
  Json.mkObj (sorted.map fun (key, count) => (key, toJson count))

def toJson (s : WalkStats) : Json :=
  Json.mkObj [
    ("phase_ms", countsToJson s.phaseMs),
    ("rejects", countsToJson s.rejects),
    ("attempts", Lean.toJson s.attempts),
    ("applications_tried", Lean.toJson s.applicationsTried),
    ("applications_succeeded", Lean.toJson s.applicationsSucceeded),
    ("dominant_reject", match s.dominantReject with
      | some (key, _) => Json.str key
      | none => Json.null)
  ]

end WalkStats

abbrev StatsRef := IO.Ref WalkStats

def StatsRef.reject (ref : StatsRef) (r : Reject) : BaseIO Unit :=
  ref.modify (·.bump r)

/-- Run `act` and add its wall time to `phase`, also when `act` throws. -/
def timed {m : Type → Type} {α : Type} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (ref : StatsRef) (phase : String) (act : m α) : m α := do
  let start ← (IO.monoMsNow : BaseIO Nat)
  try
    act
  finally
    let stop ← (IO.monoMsNow : BaseIO Nat)
    (ref.modify (·.addMs phase (stop - start)) : BaseIO Unit)

end Babel
