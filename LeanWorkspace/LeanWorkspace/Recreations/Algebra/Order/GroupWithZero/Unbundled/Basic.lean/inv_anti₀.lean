import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

