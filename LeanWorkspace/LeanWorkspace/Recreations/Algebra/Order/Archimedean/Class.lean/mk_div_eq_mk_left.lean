import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_div_eq_mk_left (h : MulArchimedeanClass.mk a < MulArchimedeanClass.mk b) : MulArchimedeanClass.mk (a / b) = MulArchimedeanClass.mk a := by
  simpa [h, div_eq_mul_inv] using MulArchimedeanClass.mk_mul_eq_mk_left (a := a) (b := b⁻¹)

