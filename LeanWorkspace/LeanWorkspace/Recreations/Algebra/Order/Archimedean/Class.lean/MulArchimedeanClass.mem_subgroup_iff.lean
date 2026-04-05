import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem mem_subgroup_iff (hs : s ≠ ⊤) : a ∈ MulArchimedeanClass.subgroup s ↔ MulArchimedeanClass.mk a ∈ s := by
  simp [MulArchimedeanClass.subgroup, MulArchimedeanClass.subsemigroup, hs]

