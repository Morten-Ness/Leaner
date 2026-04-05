import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)

theorem degree_pos_of_not_isUnit_of_dvd_monic (ha : ¬IsUnit a) (hap : a ∣ p) : 0 < degree a := by
  contrapose! ha with h
  rw [Polynomial.eq_C_of_degree_le_zero h] at hap ⊢
  simpa [hp.C_dvd_iff_isUnit, isUnit_C] using hap

