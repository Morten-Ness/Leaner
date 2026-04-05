import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem right_eq_mul₀ [IsRightCancelMulZero M₀] (hb : b ≠ 0) : b = a * b ↔ a = 1 := by
  rw [eq_comm, mul_eq_right₀ hb]

