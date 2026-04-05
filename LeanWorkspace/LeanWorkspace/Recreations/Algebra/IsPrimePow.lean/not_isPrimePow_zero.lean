import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem not_isPrimePow_zero [NoZeroDivisors R] : ¬IsPrimePow (0 : R) := by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n _hn hx
  rw [eq_zero_of_pow_eq_zero hx]
  simp

