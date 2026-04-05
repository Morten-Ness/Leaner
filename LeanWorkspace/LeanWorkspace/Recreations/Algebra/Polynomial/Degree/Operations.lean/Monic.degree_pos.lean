import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)

theorem Monic.degree_pos : 0 < degree p ↔ p ≠ 1 := natDegree_pos_iff_degree_pos.symm.trans hp.natDegree_pos

