import Mathlib

variable {M : Type*}

theorem Irreducible.not_dvd_one [CommMonoid M] {p : M} (hp : Irreducible p) : ¬p ∣ 1 := hp.not_dvd_isUnit isUnit_one

