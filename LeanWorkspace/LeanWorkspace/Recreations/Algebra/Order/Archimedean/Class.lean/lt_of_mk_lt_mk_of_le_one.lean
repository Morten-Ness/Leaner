import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem lt_of_mk_lt_mk_of_le_one (h : MulArchimedeanClass.mk a < MulArchimedeanClass.mk b) (hneg : a ≤ 1) : a < b := by
  obtain h := MulArchimedeanClass.mk_lt_mk.mp h 1
  rw [pow_one, mabs_lt, mabs_eq_inv_self.mpr hneg, inv_inv] at h
  exact h.1

