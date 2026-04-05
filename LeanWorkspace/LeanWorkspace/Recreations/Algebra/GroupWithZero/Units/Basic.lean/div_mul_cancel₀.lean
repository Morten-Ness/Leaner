import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_mul_cancel₀ (a : G₀) (h : b ≠ 0) : a / b * b = a := by simp [h]

