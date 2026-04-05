import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

theorem mul_inv_lt_of_lt_mul₀ (h : a < b * c) : a * c⁻¹ < b := by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul₀ zero_le' zero_le' h

