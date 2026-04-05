import Mathlib

variable {R A : Type*}

variable [Group R] [StarMul R]

theorem inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [isSelfAdjoint_iff, star_inv, IsSelfAdjoint.star_eq hx]

