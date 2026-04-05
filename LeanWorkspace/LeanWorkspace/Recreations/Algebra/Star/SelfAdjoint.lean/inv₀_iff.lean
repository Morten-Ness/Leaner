import Mathlib

variable {R A : Type*}

variable [GroupWithZero R] [StarMul R]

theorem inv₀_iff (x : R) : IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff]

