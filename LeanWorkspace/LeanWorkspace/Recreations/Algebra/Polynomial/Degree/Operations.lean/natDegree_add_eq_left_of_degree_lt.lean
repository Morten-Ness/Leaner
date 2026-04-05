import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_add_eq_left_of_degree_lt (h : degree q < degree p) :
    natDegree (p + q) = natDegree p := natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_left_of_degree_lt h)

