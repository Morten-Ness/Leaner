import Mathlib

variable {R A : Type*}

variable [AddGroup R] [StarAddMonoid R]

theorem isSelfAdjoint {x : selfAdjoint R} : IsSelfAdjoint (x : R) := by simp [isSelfAdjoint_iff]

