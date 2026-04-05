import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_C_mul (f : R[X]) (r : R) (N : ℕ) : Polynomial.reflect N (C r * f) = C r * Polynomial.reflect N f := by
  ext
  simp only [Polynomial.coeff_reflect, coeff_C_mul]

