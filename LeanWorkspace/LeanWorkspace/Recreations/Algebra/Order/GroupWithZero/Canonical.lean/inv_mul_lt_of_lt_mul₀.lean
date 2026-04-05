import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

theorem inv_mul_lt_of_lt_mul₀ (h : a < b * c) : b⁻¹ * a < c := by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h

