import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem mul_ne_zero_iff_left (ha : a ≠ 0) : a * b ≠ 0 ↔ b ≠ 0 := by simp [ha]

