import Mathlib

variable {R A : Type*}

variable [Group R] [StarMul R]

theorem inv_iff (x : R) : IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff]

