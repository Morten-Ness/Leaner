import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

theorem mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ c * a := by
  rw [mul_inv_le_iff₀ hc, mul_comm]

