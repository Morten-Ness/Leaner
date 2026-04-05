import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem subgroup_eq_bot : MulArchimedeanClass.subgroup (M := M) ⊤ = ⊥ := by
  simp [MulArchimedeanClass.subgroup]

