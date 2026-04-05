import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] {f : R →+* S} {p : R[X]}

theorem natDegree_map_le : natDegree (p.map f) ≤ natDegree p := natDegree_le_natDegree Polynomial.degree_map_le

