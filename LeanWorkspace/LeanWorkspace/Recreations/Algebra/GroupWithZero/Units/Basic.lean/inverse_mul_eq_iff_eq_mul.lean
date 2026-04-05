import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z := ⟨fun h1 => by rw [← h1, Ring.mul_inverse_cancel_left _ _ h],
  fun h1 => by rw [h1, Ring.inverse_mul_cancel_left _ _ h]⟩

