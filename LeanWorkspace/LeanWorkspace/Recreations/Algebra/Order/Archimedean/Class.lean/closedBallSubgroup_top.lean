import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem closedBallSubgroup_top : closedBallSubgroup (M := M) ⊤ = ⊥ := by
  ext
  simp

