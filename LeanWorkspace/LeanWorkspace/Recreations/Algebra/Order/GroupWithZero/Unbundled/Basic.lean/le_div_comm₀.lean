import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

theorem le_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a ≤ b / c ↔ c ≤ b / a := by
  rw [le_div_iff₀ ha, le_div_iff₀' hc]

