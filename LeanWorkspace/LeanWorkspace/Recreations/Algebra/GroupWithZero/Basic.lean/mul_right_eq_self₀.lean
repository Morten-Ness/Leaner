import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem mul_right_eq_self₀ [IsLeftCancelMulZero M₀] : a * b = a ↔ b = 1 ∨ a = 0 := calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff

