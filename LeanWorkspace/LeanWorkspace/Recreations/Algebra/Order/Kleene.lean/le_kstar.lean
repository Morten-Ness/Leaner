import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem le_kstar : a ≤ a∗ := le_trans (le_mul_of_one_le_left' one_le_kstar) kstar_mul_le_kstar

