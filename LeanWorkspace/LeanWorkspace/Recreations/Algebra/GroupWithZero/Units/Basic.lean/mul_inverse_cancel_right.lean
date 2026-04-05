import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * x⁻¹ʳ = y := by
  rw [mul_assoc, Ring.mul_inverse_cancel x h, mul_one]

