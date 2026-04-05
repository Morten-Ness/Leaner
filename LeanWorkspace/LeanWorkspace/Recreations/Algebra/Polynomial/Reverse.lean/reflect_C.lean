import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_C (r : R) (N : ℕ) : Polynomial.reflect N (C r) = C r * X ^ N := by
  conv_lhs => rw [← mul_one (C r), ← pow_zero X, Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_zero]

