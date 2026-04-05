import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem top_eq_mk_iff : ⊤ = MulArchimedeanClass.mk a ↔ a = 1 := by
  rw [eq_comm, MulArchimedeanClass.mk_eq_top_iff]

