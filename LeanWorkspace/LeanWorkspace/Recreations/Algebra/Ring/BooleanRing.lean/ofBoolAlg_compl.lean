import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

theorem ofBoolAlg_compl (a : AsBoolAlg α) : ofBoolAlg aᶜ = 1 + ofBoolAlg a := rfl

