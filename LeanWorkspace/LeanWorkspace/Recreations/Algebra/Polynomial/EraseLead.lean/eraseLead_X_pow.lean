import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_X_pow (n : ℕ) : Polynomial.eraseLead (Polynomial.X ^ n : R[X]) = 0 := by
  rw [X_pow_eq_monomial, Polynomial.eraseLead_monomial]

