import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem div_self {a : R} (a0 : a ≠ 0) : a / a = 1 := by
  simpa only [one_mul] using mul_div_cancel_right₀ 1 a0

