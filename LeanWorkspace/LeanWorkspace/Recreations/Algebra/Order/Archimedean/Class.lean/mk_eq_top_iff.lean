import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_eq_top_iff : MulArchimedeanClass.mk a = ⊤ ↔ a = 1 where
  mp := by simp [← MulArchimedeanClass.mk_one, MulArchimedeanClass.mk_eq_mk]
  mpr := by simp_all

