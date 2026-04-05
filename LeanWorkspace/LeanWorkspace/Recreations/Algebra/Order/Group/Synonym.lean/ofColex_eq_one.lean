import Mathlib

variable {α β : Type*}

theorem ofColex_eq_one [One α] {a : Colex α} : ofColex a = 1 ↔ a = 1 := .rfl

