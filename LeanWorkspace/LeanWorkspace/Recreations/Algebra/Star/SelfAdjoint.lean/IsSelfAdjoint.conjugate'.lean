import Mathlib

variable {R A : Type*}

variable [Semigroup R] [StarMul R]

theorem conjugate' {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (star z * x * z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, IsSelfAdjoint.star_eq hx]

