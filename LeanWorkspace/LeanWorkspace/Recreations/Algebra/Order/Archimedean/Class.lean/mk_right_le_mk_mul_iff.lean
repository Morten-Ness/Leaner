import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_right_le_mk_mul_iff : MulArchimedeanClass.mk b ≤ MulArchimedeanClass.mk (a * b) ↔ MulArchimedeanClass.mk b ≤ MulArchimedeanClass.mk a := by
  rw [mul_comm, MulArchimedeanClass.mk_left_le_mk_mul_iff]

