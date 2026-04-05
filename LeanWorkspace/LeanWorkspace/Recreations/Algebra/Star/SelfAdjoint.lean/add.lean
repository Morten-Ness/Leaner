import Mathlib

variable {R A : Type*}

variable [AddMonoid R] [StarAddMonoid R]

theorem add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x + y) := by
  simp only [isSelfAdjoint_iff, star_add, IsSelfAdjoint.star_eq hx, IsSelfAdjoint.star_eq hy]

