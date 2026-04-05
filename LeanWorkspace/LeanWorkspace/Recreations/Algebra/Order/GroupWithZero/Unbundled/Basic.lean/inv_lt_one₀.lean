import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a := by simpa using inv_mul_lt_one₀ ha (b := 1)

