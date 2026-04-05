import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

theorem mem_subgroup_iff : a ∈ FiniteMulArchimedeanClass.subgroup s ↔ ∀ h : a ≠ 1, FiniteMulArchimedeanClass.mk a h ∈ s := by
  simp_rw [FiniteMulArchimedeanClass.mk, Ne, ← MulArchimedeanClass.mk_eq_top_iff]; rfl

