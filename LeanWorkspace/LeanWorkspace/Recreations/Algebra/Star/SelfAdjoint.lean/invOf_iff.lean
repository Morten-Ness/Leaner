import Mathlib

variable {R A : Type*}

variable [Monoid R] [StarMul R]

theorem invOf_iff (x : R) [Invertible x] : IsSelfAdjoint ⅟x ↔ IsSelfAdjoint x := by
  rw [isSelfAdjoint_iff, isSelfAdjoint_iff, star_invOf, invOf_inj]

alias ⟨_, invOf⟩ := invOf_iff

