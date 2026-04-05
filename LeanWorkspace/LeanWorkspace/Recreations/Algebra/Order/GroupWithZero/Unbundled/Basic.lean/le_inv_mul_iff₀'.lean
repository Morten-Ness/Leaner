import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

theorem le_inv_mul_iff₀' (hc : 0 < c) : a ≤ c⁻¹ * b ↔ a * c ≤ b := by
  rw [le_inv_mul_iff₀ hc, mul_comm]

