import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem one_lt_div₀ (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff₀ hb, one_mul]

