import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

theorem toBoolAlg_symm_eq : (@toBoolAlg α).symm = ofBoolAlg := rfl

