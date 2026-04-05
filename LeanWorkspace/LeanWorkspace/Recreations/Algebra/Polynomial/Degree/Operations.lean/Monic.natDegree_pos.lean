import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)

theorem Monic.natDegree_pos : 0 < natDegree p ↔ p ≠ 1 := Nat.pos_iff_ne_zero.trans Polynomial.natDegree_eq_zero hp.not

