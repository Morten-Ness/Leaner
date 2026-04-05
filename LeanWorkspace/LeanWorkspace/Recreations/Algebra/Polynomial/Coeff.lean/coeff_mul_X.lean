import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_X (p : R[X]) (n : ℕ) : coeff (p * Polynomial.X) (n + 1) = coeff p n := by
  simpa only [pow_one] using Polynomial.coeff_mul_X_pow p 1 n

