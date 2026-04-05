import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

theorem degree_X_pow : Polynomial.degree ((Polynomial.X : R[X]) ^ n) = n := by
  rw [X_pow_eq_monomial, Polynomial.degree_monomial _ (one_ne_zero' R)]

