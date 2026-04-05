import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_mul_le_self : a * b ≤ b → a∗ * b ≤ b := KleeneAlgebra.kstar_mul_le_self _ _

