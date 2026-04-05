import Mathlib

variable {R A : Type*}

variable [GroupWithZero R] [StarMul R]

theorem zpow₀ {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_zpow₀, IsSelfAdjoint.star_eq hx]

