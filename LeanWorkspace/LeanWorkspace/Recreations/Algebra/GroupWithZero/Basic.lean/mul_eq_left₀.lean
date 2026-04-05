import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_eq_left₀ [IsLeftCancelMulZero M₀] (ha : a ≠ 0) : a * b = a ↔ b = 1 := by
  rw [Iff.comm, ← mul_right_inj' ha, mul_one]

