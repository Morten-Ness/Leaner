import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

theorem map_mk_le (f : M →*o N) (h : MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b) : MulArchimedeanClass.mk (f a) ≤ MulArchimedeanClass.mk (f b) := by
  rw [← MulArchimedeanClass.orderHom_mk, ← MulArchimedeanClass.orderHom_mk]
  exact OrderHomClass.monotone _ h

