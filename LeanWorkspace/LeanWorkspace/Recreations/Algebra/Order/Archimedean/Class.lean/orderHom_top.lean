import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

theorem orderHom_top (f : M →*o N) : MulArchimedeanClass.orderHom f ⊤ = ⊤ := by
  rw [← MulArchimedeanClass.mk_one, ← MulArchimedeanClass.mk_one, MulArchimedeanClass.orderHom_mk, map_one]

