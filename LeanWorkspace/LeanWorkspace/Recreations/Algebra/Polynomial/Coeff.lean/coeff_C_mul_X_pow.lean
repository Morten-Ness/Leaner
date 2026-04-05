import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff (Polynomial.C x * Polynomial.X ^ k : R[X]) n = if n = k then x else 0 := by
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  simp [eq_comm]

