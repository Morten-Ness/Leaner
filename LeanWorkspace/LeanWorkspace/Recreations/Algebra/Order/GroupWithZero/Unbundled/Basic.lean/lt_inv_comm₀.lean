import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv₀ (Right.inv_pos.2 hb) ha, inv_inv]

