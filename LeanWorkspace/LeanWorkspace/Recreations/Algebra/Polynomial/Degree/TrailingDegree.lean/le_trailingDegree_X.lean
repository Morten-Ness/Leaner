import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_trailingDegree_X : (1 : ℕ∞) ≤ Polynomial.trailingDegree (Polynomial.X : R[X]) := Polynomial.le_trailingDegree_monomial

