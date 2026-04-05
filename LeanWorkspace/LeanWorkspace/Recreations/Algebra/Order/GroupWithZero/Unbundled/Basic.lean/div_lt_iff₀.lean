import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c := by
  rw [div_eq_mul_inv, mul_inv_lt_iff₀ hc]

