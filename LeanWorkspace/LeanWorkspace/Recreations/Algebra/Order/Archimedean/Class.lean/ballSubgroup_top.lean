import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem ballSubgroup_top : ballSubgroup (M := M) ⊤ = ⊥ := by
  convert MulArchimedeanClass.subgroup_eq_bot M
  simp

