import Mathlib

variable {R A : Type*}

variable [AddCommMonoid R] [StarAddMonoid R]

theorem add_star_self (x : R) : IsSelfAdjoint (x + star x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

