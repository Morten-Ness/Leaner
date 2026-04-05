import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem one_le_kstar : 1 ≤ a∗ := KleeneAlgebra.one_le_kstar _

