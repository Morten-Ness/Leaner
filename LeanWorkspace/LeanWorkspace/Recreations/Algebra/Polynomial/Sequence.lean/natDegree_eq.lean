import Mathlib

open scoped Function

variable (R : Type*)

variable [Semiring R] (S : Sequence R)

theorem natDegree_eq (i : ℕ) : (S i).natDegree = i := natDegree_eq_of_degree_eq_some <| S.degree_eq i

