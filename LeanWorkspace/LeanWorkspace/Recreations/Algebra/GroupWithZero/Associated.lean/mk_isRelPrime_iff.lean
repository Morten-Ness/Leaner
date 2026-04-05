import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mk_isRelPrime_iff {a b : M} :
    IsRelPrime (Associates.mk a) (Associates.mk b) ↔ IsRelPrime a b := by
  simp_rw [IsRelPrime, Associates.forall_associated, Associates.mk_dvd_mk, Associates.isUnit_mk]

