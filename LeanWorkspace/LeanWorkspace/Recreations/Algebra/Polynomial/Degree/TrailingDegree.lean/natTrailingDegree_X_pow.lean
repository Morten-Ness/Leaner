import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem natTrailingDegree_X_pow (n : ℕ) :
    (Polynomial.X ^ n : R[X]).natTrailingDegree = n := by
  rw [X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial one_ne_zero]

