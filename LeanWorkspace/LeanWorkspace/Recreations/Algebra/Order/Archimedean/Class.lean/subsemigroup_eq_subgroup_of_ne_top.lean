import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem subsemigroup_eq_subgroup_of_ne_top (hs : s ≠ ⊤) :
    MulArchimedeanClass.subsemigroup s = (MulArchimedeanClass.subgroup s : Set M) := by
  simp [MulArchimedeanClass.subgroup, hs]

