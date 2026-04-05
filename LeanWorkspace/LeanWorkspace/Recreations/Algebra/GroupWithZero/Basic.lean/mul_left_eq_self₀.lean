import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_left_eq_self₀ [IsRightCancelMulZero M₀] : a * b = b ↔ a = 1 ∨ b = 0 := calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff

