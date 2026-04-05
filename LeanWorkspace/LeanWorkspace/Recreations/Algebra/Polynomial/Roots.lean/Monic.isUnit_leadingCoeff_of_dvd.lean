import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem Monic.isUnit_leadingCoeff_of_dvd {a p : R[X]} (hp : Monic p) (hap : a ∣ p) :
    IsUnit a.leadingCoeff := isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)

