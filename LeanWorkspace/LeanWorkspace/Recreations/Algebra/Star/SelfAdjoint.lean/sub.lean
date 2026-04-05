import Mathlib

variable {R A : Type*}

variable [AddGroup R] [StarAddMonoid R]

theorem sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x - y) := by
  simp only [isSelfAdjoint_iff, star_sub, IsSelfAdjoint.star_eq hx, IsSelfAdjoint.star_eq hy]

