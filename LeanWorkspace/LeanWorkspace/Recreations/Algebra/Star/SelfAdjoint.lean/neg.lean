import Mathlib

variable {R A : Type*}

variable [AddGroup R] [StarAddMonoid R]

theorem neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-x) := by
  simp only [isSelfAdjoint_iff, star_neg, IsSelfAdjoint.star_eq hx]

