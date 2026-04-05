import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

theorem toBoolAlg_inj {a b : α} : toBoolAlg a = toBoolAlg b ↔ a = b := Iff.rfl

