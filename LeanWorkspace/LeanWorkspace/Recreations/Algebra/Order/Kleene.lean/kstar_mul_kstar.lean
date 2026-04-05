import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_mul_kstar (a : α) : a∗ * a∗ = a∗ := (mul_kstar_le le_rfl <| kstar_mul_le_kstar).antisymm <| le_mul_of_one_le_left' one_le_kstar

