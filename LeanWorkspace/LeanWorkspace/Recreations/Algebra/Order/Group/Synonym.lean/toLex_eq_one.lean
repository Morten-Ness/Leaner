import Mathlib

variable {α β : Type*}

theorem toLex_eq_one [One α] {a : α} : toLex a = 1 ↔ a = 1 := .rfl

