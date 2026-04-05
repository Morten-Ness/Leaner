import Mathlib

variable {R A : Type*}

variable [CommSemigroup R] [StarMul R]

theorem mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x * y) := by
  simp only [isSelfAdjoint_iff, star_mul', IsSelfAdjoint.star_eq hx, IsSelfAdjoint.star_eq hy]

