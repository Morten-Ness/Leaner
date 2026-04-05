import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_left_le_mk_div_iff : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk (a / b) ↔ MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b where
  mp h := by simpa using MulArchimedeanClass.mk_left_le_mk_div h
  mpr := MulArchimedeanClass.mk_left_le_mk_div

