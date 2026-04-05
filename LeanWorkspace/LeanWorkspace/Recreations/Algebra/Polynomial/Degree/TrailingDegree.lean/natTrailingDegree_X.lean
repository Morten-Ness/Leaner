import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem natTrailingDegree_X : (Polynomial.X : R[X]).natTrailingDegree = 1 := Polynomial.natTrailingDegree_monomial one_ne_zero

