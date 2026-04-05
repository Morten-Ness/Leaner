import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [div_lt_iff₀ hc, div_mul_cancel₀ _ hc.ne']

