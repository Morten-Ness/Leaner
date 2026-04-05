import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem dvd_of_mk_le_mk {a b : M} : Associates.mk a ≤ Associates.mk b → a ∣ b := Associates.mk_dvd_mk.mp

