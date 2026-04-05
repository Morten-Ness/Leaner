import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem left_eq_mul₀ [IsLeftCancelMulZero M₀] (ha : a ≠ 0) : a = a * b ↔ b = 1 := by
  rw [eq_comm, mul_eq_left₀ ha]

