import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

theorem lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  rw [lt_div_iff₀ hc, mul_comm]

