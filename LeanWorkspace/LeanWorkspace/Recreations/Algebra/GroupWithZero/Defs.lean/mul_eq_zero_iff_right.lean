import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem mul_eq_zero_iff_right (hb : b ≠ 0) : a * b = 0 ↔ a = 0 := by simp [hb]

