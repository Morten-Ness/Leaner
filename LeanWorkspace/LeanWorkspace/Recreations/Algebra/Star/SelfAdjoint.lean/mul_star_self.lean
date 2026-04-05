import Mathlib

variable {R A : Type*}

theorem mul_star_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (x * star x) := by
  simpa only [star_star] using IsSelfAdjoint.star_mul_self (star x)

