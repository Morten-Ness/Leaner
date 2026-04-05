import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem natDegree_X_add_C (x : R) : (Polynomial.X + Polynomial.C x).natDegree = 1 := natDegree_eq_of_degree_eq_some <| Polynomial.degree_X_add_C x

