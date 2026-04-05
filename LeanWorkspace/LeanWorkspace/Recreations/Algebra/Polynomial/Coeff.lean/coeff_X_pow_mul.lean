import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_X_pow_mul (p : R[X]) (n d : ℕ) :
    coeff (Polynomial.X ^ n * p) (d + n) = coeff p d := by
  rw [(commute_X_pow p n).eq, Polynomial.coeff_mul_X_pow]

