import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)

theorem natDegree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < natDegree a := natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_not_isUnit_of_dvd_monic hp ha hap

