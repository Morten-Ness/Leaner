import Mathlib

variable {M : Type*}

theorem Irreducible.not_dvd_isUnit [CommMonoid M] {p u : M} (hp : Irreducible p) (hu : IsUnit u) :
    ¬p ∣ u := mt (isUnit_of_dvd_unit · hu) hp.not_isUnit

