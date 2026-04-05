import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)

theorem Monic.C_dvd_iff_isUnit {a : R} : Polynomial.C a ∣ p ↔ IsUnit a where
  mp h := isUnit_iff_dvd_one.mpr <| hp.coeff_natDegree ▸ (C_dvd_iff_dvd_coeff _ _).mp h p.natDegree
  mpr ha := (ha.map Polynomial.C).dvd

