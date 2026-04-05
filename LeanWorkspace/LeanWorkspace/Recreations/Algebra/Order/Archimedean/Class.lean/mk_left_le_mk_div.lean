import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_left_le_mk_div (hab : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b) : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk (a / b) := by
  simpa [div_eq_mul_inv, hab] using MulArchimedeanClass.mk_left_le_mk_mul (a := a) (b := b⁻¹)

