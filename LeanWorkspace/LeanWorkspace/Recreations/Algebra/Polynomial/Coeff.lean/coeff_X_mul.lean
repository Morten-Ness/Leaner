import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_X_mul (p : R[X]) (n : ℕ) : coeff (Polynomial.X * p) (n + 1) = coeff p n := by
  rw [(commute_X p).eq, Polynomial.coeff_mul_X]

