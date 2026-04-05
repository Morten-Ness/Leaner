import Mathlib

variable {R A : Type*}

variable [Monoid R] [StarMul R]

theorem pow {x : R} (hx : IsSelfAdjoint x) (n : ℕ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_pow, IsSelfAdjoint.star_eq hx]

