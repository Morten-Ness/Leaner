import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_mul_le_kstar : a∗ * a ≤ a∗ := KleeneAlgebra.kstar_mul_le_kstar _

