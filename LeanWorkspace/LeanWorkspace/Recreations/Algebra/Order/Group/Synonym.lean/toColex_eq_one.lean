import Mathlib

variable {α β : Type*}

theorem toColex_eq_one [One α] {a : α} : toColex a = 1 ↔ a = 1 := .rfl

