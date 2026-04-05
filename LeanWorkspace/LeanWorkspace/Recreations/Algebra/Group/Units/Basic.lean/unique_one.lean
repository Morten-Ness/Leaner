import Mathlib

variable {α : Type u}

theorem unique_one {α : Type*} [Unique α] [One α] : default = (1 : α) := Unique.default_eq 1

