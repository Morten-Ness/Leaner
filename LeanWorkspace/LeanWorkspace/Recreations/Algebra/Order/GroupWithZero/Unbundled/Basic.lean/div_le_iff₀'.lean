import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

theorem div_le_iff₀' (hc : 0 < c) : b / c ≤ a ↔ b ≤ c * a := by
  rw [div_le_iff₀ hc, mul_comm]

