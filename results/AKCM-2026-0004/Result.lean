import Mathlib.Init

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: String.Slice.Pos.isValidForSlice (String)
-- Step 3: String.Pos.Raw.IsValidForSlice.le_rawEndPos (String)
theorem akcm_2026_0004
    {s : String.Slice}
    (self : s.Pos) :
    self.offset ≤ s.rawEndPos :=
  @String.Pos.Raw.IsValidForSlice.le_rawEndPos s (@String.Slice.Pos.offset s self)
  (@String.Slice.Pos.isValidForSlice s self)
