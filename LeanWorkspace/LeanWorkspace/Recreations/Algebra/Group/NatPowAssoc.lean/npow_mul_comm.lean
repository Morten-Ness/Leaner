import Mathlib

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul_comm (m n : ℕ) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← npow_add, add_comm]

