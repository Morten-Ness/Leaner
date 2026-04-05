import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem prime_mk {p : M} : Prime (Associates.mk p) ↔ Prime p := by
  rw [Prime, _root_.Prime, Associates.forall_associated]
  simp only [Associates.forall_associated, Associates.mk_ne_zero, Associates.isUnit_mk, Associates.mk_mul_mk, Associates.mk_dvd_mk]

