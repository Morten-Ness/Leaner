import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_monomial (p : R[X]) (n d : ℕ) (r : R) :
    coeff (p * monomial n r) (d + n) = coeff p d * r := by
  rw [← C_mul_X_pow_eq_monomial, ← X_pow_mul, ← mul_assoc, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_pow]

