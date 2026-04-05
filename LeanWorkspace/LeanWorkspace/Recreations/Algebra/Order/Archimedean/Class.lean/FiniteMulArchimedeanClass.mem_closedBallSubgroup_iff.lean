import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

theorem mem_closedBallSubgroup_iff {a : M} {c : FiniteMulArchimedeanClass M} :
    a ∈ closedBallSubgroup c ↔ ∀ h : a ≠ 1, c ≤ FiniteMulArchimedeanClass.mk a h := by
  simp

