import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_modByMonic_le_left : natDegree (p %ₘ q) ≤ natDegree p := natDegree_le_natDegree Polynomial.degree_modByMonic_le_left

