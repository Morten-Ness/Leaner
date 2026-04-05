import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [CommGroupWithZero G₀] [Preorder G₀] {a b c : G₀}

theorem le_mul_div_mul_left (h : a / b ≤ 0) : a / b ≤ c * a / (c * b) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

