import Mathlib

variable {M : Type*}

theorem mk_eq_one [Monoid M] {a : M} : Associates.mk a = 1 ↔ IsUnit a := by
  simpa using Associates.mk_eq_one_iff_unit a
