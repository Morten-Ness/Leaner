import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_C_mul_X_pow (r : R) (n : ℕ) : Polynomial.eraseLead (Polynomial.C r * Polynomial.X ^ n) = 0 := by
  rw [C_mul_X_pow_eq_monomial, Polynomial.eraseLead_monomial]

