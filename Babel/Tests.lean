import Babel.Stats

/-!
Build-time checks for the pure parts of the generator.
Run with `lake build BabelTest`; a failing `#guard` fails the build.
-/

open Babel

#guard (({} : WalkStats).bump .selfReuse |>.bump .selfReuse).rejects.getD "self_reuse" 0 == 2
#guard (({} : WalkStats).addMs "search" 40 |>.addMs "search" 2).phaseMs.getD "search" 0 == 42
#guard (({} : WalkStats).bump .closedByExact |>.bump .paddedFact |>.bump .paddedFact).dominantReject
  == some ("padded_fact", 2)
#guard ({} : WalkStats).dominantReject == none
