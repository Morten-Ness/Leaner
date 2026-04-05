import Mathlib

variable {R : Type*}

variable [Ring R]

theorem Splits.neg {f : R[X]} (hf : Polynomial.Splits f) : Polynomial.Splits (-f) := by
  rw [← neg_one_mul, ← C_1, ← C_neg]
  exact hf.C_mul (-1)

