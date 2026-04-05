import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹ := (inv_lt_inv₀ (hb.trans hba) hb).2 hba

