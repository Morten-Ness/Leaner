import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff₀ hc]

