import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

theorem ofBoolAlg_toBoolAlg (a : α) : ofBoolAlg (toBoolAlg a) = a := rfl

