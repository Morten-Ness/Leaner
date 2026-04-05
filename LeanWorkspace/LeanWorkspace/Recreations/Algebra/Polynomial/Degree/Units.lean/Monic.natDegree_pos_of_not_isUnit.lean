import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)

theorem Monic.natDegree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < natDegree p := hp.natDegree_pos.mpr fun hp' ↦ (hp' ▸ hu) isUnit_one

