import Mathlib

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul' (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact npow_mul x n m

