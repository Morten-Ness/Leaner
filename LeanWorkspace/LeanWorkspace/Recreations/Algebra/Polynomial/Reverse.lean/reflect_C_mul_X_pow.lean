import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_C_mul_X_pow (N n : ℕ) {c : R} : Polynomial.reflect N (C c * X ^ n) = C c * X ^ Polynomial.revAt N n := by
  ext
  grind

