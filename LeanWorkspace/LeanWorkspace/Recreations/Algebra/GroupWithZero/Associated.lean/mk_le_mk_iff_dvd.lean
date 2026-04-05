import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mk_le_mk_iff_dvd {a b : M} : Associates.mk a ≤ Associates.mk b ↔ a ∣ b := Associates.mk_dvd_mk

