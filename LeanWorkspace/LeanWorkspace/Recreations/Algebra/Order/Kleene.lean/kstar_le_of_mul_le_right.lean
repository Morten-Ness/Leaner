import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_le_of_mul_le_right (hb : 1 ≤ b) : a * b ≤ b → a∗ ≤ b := by
  simpa using kstar_mul_le hb

