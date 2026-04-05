import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c := by
  rw [← mul_lt_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

