import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_pos_iff_degree_pos : 0 < Polynomial.natDegree p ↔ 0 < Polynomial.degree p := lt_iff_lt_of_le_iff_le Polynomial.natDegree_le_iff_degree_le

