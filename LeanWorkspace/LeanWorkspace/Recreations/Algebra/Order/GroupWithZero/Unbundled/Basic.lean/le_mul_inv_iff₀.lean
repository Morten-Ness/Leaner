import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem le_mul_inv_iff₀ (hc : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b := by
  rw [← mul_le_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

