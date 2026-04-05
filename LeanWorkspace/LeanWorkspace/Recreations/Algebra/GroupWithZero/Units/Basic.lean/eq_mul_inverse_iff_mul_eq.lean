import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * z⁻¹ʳ ↔ x * z = y := ⟨fun h1 => by rw [h1, Ring.inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, Ring.mul_inverse_cancel_right _ _ h]⟩

