import Mathlib

variable {F α β : Type*}

theorem IsSquare.one [MulOneClass α] : IsSquare (1 : α) := ⟨1, (mul_one _).symm⟩

grind_pattern IsSquare.one => IsSquare (1 : α)
grind_pattern Even.zero => Even (0 : α)

