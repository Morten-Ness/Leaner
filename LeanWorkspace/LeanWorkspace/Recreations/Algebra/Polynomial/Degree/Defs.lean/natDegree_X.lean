import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]}

theorem natDegree_X : (Polynomial.X : R[X]).natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some Polynomial.degree_X

