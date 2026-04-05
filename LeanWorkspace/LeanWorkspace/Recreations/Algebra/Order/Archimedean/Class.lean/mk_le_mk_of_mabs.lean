import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem mk_le_mk_of_mabs {a b : M} (h : |a|ₘ ≤ |b|ₘ) : MulArchimedeanClass.mk b ≤ MulArchimedeanClass.mk a := by
  rw [← MulArchimedeanClass.mk_mabs a, ← MulArchimedeanClass.mk_mabs]
  have ha := one_le_mabs a
  exact MulArchimedeanClass.mk_antitoneOn ha (ha.trans h) h

