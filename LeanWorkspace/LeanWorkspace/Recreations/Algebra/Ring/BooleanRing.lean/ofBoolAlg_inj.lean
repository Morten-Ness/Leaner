import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

theorem ofBoolAlg_inj {a b : AsBoolAlg α} : ofBoolAlg a = ofBoolAlg b ↔ a = b := Iff.rfl

