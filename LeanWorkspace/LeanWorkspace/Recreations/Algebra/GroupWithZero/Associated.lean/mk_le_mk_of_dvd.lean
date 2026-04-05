import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mk_le_mk_of_dvd {a b : M} : a ∣ b → Associates.mk a ≤ Associates.mk b := Associates.mk_dvd_mk.mpr

