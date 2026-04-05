import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_left_le_mk_mul (hab : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b) : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk (a * b) := by
  simpa [hab] using MulArchimedeanClass.min_le_mk_mul (a := a) (b := b)

