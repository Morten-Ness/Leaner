import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_trailingDegree_C_mul_X_pow (n : ℕ) (a : R) :
    (n : ℕ∞) ≤ Polynomial.trailingDegree (Polynomial.C a * Polynomial.X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  exact Polynomial.le_trailingDegree_monomial

