import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hac ((inv_le_inv₀ (hd.trans_le hdb) hd).2 hdb)
    (Right.inv_nonneg.2 <| hd.le.trans hdb) hc

