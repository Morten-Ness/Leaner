import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_le_of_mul_le_left (hb : 1 ≤ b) : b * a ≤ b → a∗ ≤ b := by
  simpa using mul_kstar_le hb

