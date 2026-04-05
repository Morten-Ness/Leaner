import Mathlib

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | zero => rw [npow_zero, mul_zero, npow_zero]
  | succ n ih => rw [mul_add, npow_add, ih, mul_one, npow_add, npow_one]

