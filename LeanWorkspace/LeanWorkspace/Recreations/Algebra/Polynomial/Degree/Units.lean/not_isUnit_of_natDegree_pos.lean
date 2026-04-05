import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem not_isUnit_of_natDegree_pos (p : R[X]) (hpl : 0 < p.natDegree) : ¬ IsUnit p := Polynomial.not_isUnit_of_degree_pos _ (natDegree_pos_iff_degree_pos.mp hpl)

