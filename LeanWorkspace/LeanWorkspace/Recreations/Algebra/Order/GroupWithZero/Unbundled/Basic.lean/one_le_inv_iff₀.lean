import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

theorem one_le_inv_iff₀ : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

