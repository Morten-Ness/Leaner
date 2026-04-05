import Mathlib

open scoped Polynomial

variable {R : Type*} [Ring R]

theorem reflect_neg (f : R[X]) (N : ℕ) : Polynomial.reflect N (-f) = -Polynomial.reflect N f := by
  rw [neg_eq_neg_one_mul, ← C_1, ← C_neg, Polynomial.reflect_C_mul, C_neg, C_1, ← neg_eq_neg_one_mul]

