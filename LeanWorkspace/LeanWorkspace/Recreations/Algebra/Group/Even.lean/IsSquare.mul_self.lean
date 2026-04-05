import Mathlib

variable {F α β : Type*}

variable [Mul α]

theorem IsSquare.mul_self (r : α) : IsSquare (r * r) := ⟨r, rfl⟩

