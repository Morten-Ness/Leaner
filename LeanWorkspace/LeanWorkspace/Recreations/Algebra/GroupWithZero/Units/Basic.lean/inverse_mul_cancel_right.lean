import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * x⁻¹ʳ * x = y := by
  rw [mul_assoc, Ring.inverse_mul_cancel x h, mul_one]

