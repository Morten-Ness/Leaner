import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_mul_eq_mk_right (h : MulArchimedeanClass.mk b < MulArchimedeanClass.mk a) : MulArchimedeanClass.mk (a * b) = MulArchimedeanClass.mk b := mul_comm a b ▸ MulArchimedeanClass.mk_mul_eq_mk_left h

