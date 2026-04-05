import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_linear_le : natDegree (Polynomial.C a * Polynomial.X + Polynomial.C b) ≤ 1 := natDegree_le_of_degree_le Polynomial.degree_linear_le

