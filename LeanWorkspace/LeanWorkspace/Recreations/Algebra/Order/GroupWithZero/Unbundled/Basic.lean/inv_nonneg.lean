import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, Right.inv_pos, zero_eq_inv]

