import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem trailingDegree_X : Polynomial.trailingDegree (Polynomial.X : R[X]) = 1 := Polynomial.trailingDegree_monomial one_ne_zero

