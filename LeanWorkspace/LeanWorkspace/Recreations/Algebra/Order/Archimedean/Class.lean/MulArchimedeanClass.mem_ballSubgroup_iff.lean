import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem mem_ballSubgroup_iff {a : M} {c : MulArchimedeanClass M} (hA : c ≠ ⊤) :
    a ∈ ballSubgroup c ↔ c < MulArchimedeanClass.mk a := by
  simp [hA]

