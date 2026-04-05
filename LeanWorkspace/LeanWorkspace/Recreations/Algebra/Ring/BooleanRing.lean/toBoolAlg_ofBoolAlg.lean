import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

theorem toBoolAlg_ofBoolAlg (a : AsBoolAlg α) : toBoolAlg (ofBoolAlg a) = a := rfl

