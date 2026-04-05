import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

theorem ofBoolAlg_top : ofBoolAlg (⊤ : AsBoolAlg α) = 1 := rfl

