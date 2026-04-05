import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem mul_kstar_le_kstar : a * a∗ ≤ a∗ := KleeneAlgebra.mul_kstar_le_kstar _

