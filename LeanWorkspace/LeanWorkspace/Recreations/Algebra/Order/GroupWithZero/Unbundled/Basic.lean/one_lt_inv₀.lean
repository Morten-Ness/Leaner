import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1 := by simpa using one_lt_inv_mul₀ ha (b := 1)

