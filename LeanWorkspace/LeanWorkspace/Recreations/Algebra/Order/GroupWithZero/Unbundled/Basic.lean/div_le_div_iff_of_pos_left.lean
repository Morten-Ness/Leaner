import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b := by
  simp only [div_eq_mul_inv, mul_le_mul_iff_right₀ ha, inv_le_inv₀ hb hc]

