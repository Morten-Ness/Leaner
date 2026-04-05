import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_one : (1 : α)∗ = 1 := kstar_eq_one.2 le_rfl

