import Mathlib

variable {M : Type*}

theorem Irreducible.not_dvd_unit [CommMonoid M] {p : M} (u : Mˣ) (hp : Irreducible p) :
    ¬ p ∣ u := hp.not_dvd_isUnit u.isUnit

