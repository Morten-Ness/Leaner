import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem mem_closedBallSubgroup_iff {a : M} {c : MulArchimedeanClass M} :
    a ∈ closedBallSubgroup c ↔ c ≤ MulArchimedeanClass.mk a := by
  simp

