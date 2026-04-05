import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (x⁻¹ʳ * y) = y := by
  rw [← mul_assoc, Ring.mul_inverse_cancel x h, one_mul]

