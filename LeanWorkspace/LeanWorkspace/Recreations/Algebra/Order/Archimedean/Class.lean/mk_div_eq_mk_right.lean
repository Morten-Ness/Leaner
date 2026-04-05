import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_div_eq_mk_right (h : MulArchimedeanClass.mk b < MulArchimedeanClass.mk a) : MulArchimedeanClass.mk (a / b) = MulArchimedeanClass.mk b := by
  simpa [h, div_eq_mul_inv] using MulArchimedeanClass.mk_mul_eq_mk_right (a := a) (b := b⁻¹)

