import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_div_lt_mk_right_iff : MulArchimedeanClass.mk (a / b) < MulArchimedeanClass.mk b ↔ MulArchimedeanClass.mk a < MulArchimedeanClass.mk b := le_iff_le_iff_lt_iff_lt.1 MulArchimedeanClass.mk_right_le_mk_div_iff

