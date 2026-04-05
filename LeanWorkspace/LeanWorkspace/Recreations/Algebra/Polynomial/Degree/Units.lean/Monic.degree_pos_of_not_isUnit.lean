import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)

theorem Monic.degree_pos_of_not_isUnit (hu : ¬IsUnit p) : 0 < degree p := hp.degree_pos.mpr fun hp' ↦ (hp' ▸ hu) isUnit_one

