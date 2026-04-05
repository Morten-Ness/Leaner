import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := one_div a ▸ inv_nonneg

