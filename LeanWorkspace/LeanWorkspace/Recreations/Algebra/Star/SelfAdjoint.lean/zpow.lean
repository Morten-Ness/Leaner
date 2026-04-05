import Mathlib

variable {R A : Type*}

variable [Group R] [StarMul R]

theorem zpow {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_zpow, IsSelfAdjoint.star_eq hx]

