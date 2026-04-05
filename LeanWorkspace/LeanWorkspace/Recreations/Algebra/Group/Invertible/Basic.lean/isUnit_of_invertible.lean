import Mathlib

variable {α : Type u}

theorem isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a := ⟨unitOfInvertible a, rfl⟩

