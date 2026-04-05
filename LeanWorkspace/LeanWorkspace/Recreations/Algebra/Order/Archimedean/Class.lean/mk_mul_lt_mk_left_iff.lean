import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_mul_lt_mk_left_iff : MulArchimedeanClass.mk (a * b) < MulArchimedeanClass.mk a ↔ MulArchimedeanClass.mk b < MulArchimedeanClass.mk a := le_iff_le_iff_lt_iff_lt.1 MulArchimedeanClass.mk_left_le_mk_mul_iff

