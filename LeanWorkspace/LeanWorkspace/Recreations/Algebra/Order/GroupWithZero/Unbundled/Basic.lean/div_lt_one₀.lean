import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem div_lt_one₀ (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff₀ hb, one_mul]

