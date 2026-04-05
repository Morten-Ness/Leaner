import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

theorem div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  rw [div_lt_iff₀ hb, div_lt_iff₀' hc]

