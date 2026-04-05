import Mathlib

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul_assoc (k m n : ℕ) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← npow_add, add_assoc]

