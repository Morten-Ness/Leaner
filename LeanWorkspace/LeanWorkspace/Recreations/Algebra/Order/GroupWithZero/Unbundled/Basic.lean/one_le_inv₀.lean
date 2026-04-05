import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem one_le_inv₀ (ha : 0 < a) : 1 ≤ a⁻¹ ↔ a ≤ 1 := by simpa using one_le_inv_mul₀ ha (b := 1)

