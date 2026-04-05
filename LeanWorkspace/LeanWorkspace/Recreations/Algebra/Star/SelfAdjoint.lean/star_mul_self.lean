import Mathlib

variable {R A : Type*}

theorem star_mul_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (star x * x) := by
  simp only [IsSelfAdjoint, star_mul, star_star]

