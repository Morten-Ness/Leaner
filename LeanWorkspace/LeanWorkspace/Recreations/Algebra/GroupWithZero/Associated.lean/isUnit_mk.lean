import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem isUnit_mk {a : M} : IsUnit (Associates.mk a) ↔ IsUnit a := calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [Associates.isUnit_iff_eq_one, Associates.one_eq_mk_one, Associates.mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_isUnit

