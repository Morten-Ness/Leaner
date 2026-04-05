import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem out_top : (⊤ : MulArchimedeanClass M).out = 1 := by
  rw [← MulArchimedeanClass.mk_eq_top_iff, MulArchimedeanClass.mk_out]

