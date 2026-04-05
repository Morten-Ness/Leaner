import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_sub_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p - q) = natDegree p := natDegree_eq_of_degree_eq (Polynomial.degree_sub_eq_left_of_degree_lt (Polynomial.degree_lt_degree h))

