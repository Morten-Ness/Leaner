import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem min_le_mk_div (a b : M) : min (MulArchimedeanClass.mk a) (MulArchimedeanClass.mk b) ≤ MulArchimedeanClass.mk (a / b) := by
  simpa [div_eq_mul_inv] using MulArchimedeanClass.min_le_mk_mul (a := a) (b := b⁻¹)

