import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem lt_of_mk_lt_mk_of_one_le (h : MulArchimedeanClass.mk a < MulArchimedeanClass.mk b) (hpos : 1 ≤ a) : b < a := by
  obtain h := MulArchimedeanClass.mk_lt_mk.mp h 1
  rw [pow_one, mabs_lt, mabs_eq_self.mpr hpos] at h
  exact h.2

