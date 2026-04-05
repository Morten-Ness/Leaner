import Mathlib

variable {R A : Type*}

variable [AddCommMonoid R] [StarAddMonoid R]

theorem star_add_self (x : R) : IsSelfAdjoint (star x + x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

