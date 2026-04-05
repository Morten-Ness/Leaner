import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : x⁻¹ʳ * (x * y) = y := by
  rw [← mul_assoc, Ring.inverse_mul_cancel x h, one_mul]

