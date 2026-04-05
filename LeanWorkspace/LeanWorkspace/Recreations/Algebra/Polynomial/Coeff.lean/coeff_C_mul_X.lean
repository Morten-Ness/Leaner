import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_C_mul_X (x : R) (n : ℕ) : coeff (Polynomial.C x * Polynomial.X : R[X]) n = if n = 1 then x else 0 := by
  rw [← pow_one Polynomial.X, Polynomial.coeff_C_mul_X_pow]

