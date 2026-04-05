import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem le_inv_mul_iff₀ (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b := by
  rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

