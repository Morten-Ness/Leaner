import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

theorem ofBoolAlg_symm_eq : (@ofBoolAlg α).symm = toBoolAlg := rfl

