import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b ≠ 0) : a * b = b ↔ a = 1 := by
  rw [Iff.comm, ← mul_left_inj' hb, one_mul]

