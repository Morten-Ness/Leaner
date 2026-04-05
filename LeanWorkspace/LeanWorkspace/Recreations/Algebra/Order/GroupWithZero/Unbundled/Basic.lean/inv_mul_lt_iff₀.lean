import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a := by
  rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

