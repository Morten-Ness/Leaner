import Mathlib

variable {R A : Type*}

variable [GroupWithZero R] [StarMul R]

theorem inv₀ {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [isSelfAdjoint_iff, star_inv₀, IsSelfAdjoint.star_eq hx]

