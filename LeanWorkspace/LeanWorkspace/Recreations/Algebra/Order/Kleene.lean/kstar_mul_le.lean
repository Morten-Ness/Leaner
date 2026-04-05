import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_mul_le (hb : b ≤ c) (ha : a * c ≤ c) : a∗ * b ≤ c := by grw [hb, kstar_mul_le_self ha]

