import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem trailingDegree_X_pow (n : ℕ) :
    (Polynomial.X ^ n : R[X]).trailingDegree = n := by
  rw [X_pow_eq_monomial, Polynomial.trailingDegree_monomial one_ne_zero]

