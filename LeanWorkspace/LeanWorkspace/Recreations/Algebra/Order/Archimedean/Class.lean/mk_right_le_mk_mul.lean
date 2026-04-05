import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_right_le_mk_mul (hba : MulArchimedeanClass.mk b ≤ MulArchimedeanClass.mk a) : MulArchimedeanClass.mk b ≤ MulArchimedeanClass.mk (a * b) := by
  simpa [hba] using MulArchimedeanClass.min_le_mk_mul (a := a) (b := b)

