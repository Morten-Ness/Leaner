import Mathlib

variable {R A : Type*}

variable [Semifield R] [StarRing R]

theorem div {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x / y) := by
  simp only [isSelfAdjoint_iff, star_div₀, IsSelfAdjoint.star_eq hx, IsSelfAdjoint.star_eq hy]

