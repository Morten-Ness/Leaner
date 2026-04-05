import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

theorem subgroup_eq_bot : FiniteMulArchimedeanClass.subgroup (M := M) ⊤ = ⊥ := by
  ext; simp [FiniteMulArchimedeanClass.subgroup, MulArchimedeanClass.subsemigroup, FiniteMulArchimedeanClass.toUpperSetMulArchimedeanClass]

