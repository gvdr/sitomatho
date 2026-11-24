import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Regular.Defs
import Mathlib.Algebra.Regular.Opposite
import Mathlib.Algebra.Regular.SMul

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: IsAddLeftRegular.unop (IsAddLeftRegular)
-- Step 1: IsAddRightRegular.op (IsAddRightRegular)
-- Step 2: IsAddLeftRegular.op (IsAddLeftRegular)
-- Step 3: IsAddRightRegular.op (IsAddRightRegular)
-- Step 4: IsAddRightRegular.isVAddRegular (IsAddRightRegular)
theorem akcm_2026_0003
    {R : Type}
    [inst_2 : Add R]
    {a : Rᵃᵒᵖ}
    (h_4 : IsAddRightRegular a) :
    IsVAddRegular Rᵃᵒᵖᵃᵒᵖᵃᵒᵖ
  (AddOpposite.op
    (AddOpposite.op (AddOpposite.op (AddOpposite.op (AddOpposite.unop a))))) :=
  @IsAddRightRegular.isVAddRegular.{0} (AddOpposite.{0} (AddOpposite.{0} (AddOpposite.{0} R)))
  (@AddOpposite.instAdd.{0} (AddOpposite.{0} (AddOpposite.{0} R))
    (@AddOpposite.instAdd.{0} (AddOpposite.{0} R) (@AddOpposite.instAdd.{0} R inst_2)))
  (@AddOpposite.op.{0} (AddOpposite.{0} (AddOpposite.{0} R))
    (@AddOpposite.op.{0} (AddOpposite.{0} R)
      (@AddOpposite.op.{0} R (@AddOpposite.unop.{0} R a))))
  (@IsAddRightRegular.op.{0} (AddOpposite.{0} (AddOpposite.{0} R))
    (@AddOpposite.instAdd.{0} (AddOpposite.{0} R) (@AddOpposite.instAdd.{0} R inst_2))
    (@AddOpposite.op.{0} (AddOpposite.{0} R)
      (@AddOpposite.op.{0} R (@AddOpposite.unop.{0} R a)))
    (@IsAddLeftRegular.op.{0} (AddOpposite.{0} R) (@AddOpposite.instAdd.{0} R inst_2)
      (@AddOpposite.op.{0} R (@AddOpposite.unop.{0} R a))
      (@IsAddRightRegular.op.{0} R inst_2 (@AddOpposite.unop.{0} R a)
        (@IsAddLeftRegular.unop.{0} R inst_2 a h_4))))
