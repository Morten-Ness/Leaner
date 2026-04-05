import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem div_lt_div₀ (hac : a < c) (hdb : d ≤ b) (hc : 0 ≤ c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_lt_mul hac (by gcongr; assumption) _ hc
  exact Right.inv_pos.2 (hd.trans_le hdb)

