import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mk_isRelPrime_iff {a b : M} :
    IsRelPrime (Associates.mk a) (Associates.mk b) ↔ IsRelPrime a b := by
  simpa using Associates.mk_relPrime_mk_iff_relPrime a b
