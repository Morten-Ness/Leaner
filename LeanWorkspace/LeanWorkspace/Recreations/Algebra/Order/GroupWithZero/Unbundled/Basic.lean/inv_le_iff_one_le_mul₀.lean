import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [← mul_inv_le_iff₀ ha, one_mul]

