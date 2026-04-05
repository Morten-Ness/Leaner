import Mathlib

variable {M : Type*}

theorem mk_eq_one [Monoid M] {a : M} : Associates.mk a = 1 ↔ IsUnit a := by
  rw [← Associates.mk_one, Associates.mk_eq_mk_iff_associated, associated_one_iff_isUnit]

