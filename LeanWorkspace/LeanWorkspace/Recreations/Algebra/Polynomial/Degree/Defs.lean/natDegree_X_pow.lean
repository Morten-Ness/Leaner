import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

theorem natDegree_X_pow : Polynomial.natDegree ((Polynomial.X : R[X]) ^ n) = n := Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_X_pow n)

