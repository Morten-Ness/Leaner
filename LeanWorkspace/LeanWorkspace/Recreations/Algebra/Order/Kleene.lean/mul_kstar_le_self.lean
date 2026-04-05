import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem mul_kstar_le_self : b * a ≤ b → b * a∗ ≤ b := KleeneAlgebra.mul_kstar_le_self _ _

