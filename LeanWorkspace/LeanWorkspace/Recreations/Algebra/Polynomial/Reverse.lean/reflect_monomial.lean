import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_monomial (N n : ℕ) : Polynomial.reflect N ((X : R[X]) ^ n) = X ^ Polynomial.revAt N n := by
  rw [← one_mul (X ^ n), ← one_mul (X ^ Polynomial.revAt N n), ← C_1, Polynomial.reflect_C_mul_X_pow]

