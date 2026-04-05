import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

theorem ofBoolAlg_bot : ofBoolAlg (⊥ : AsBoolAlg α) = 0 := rfl

