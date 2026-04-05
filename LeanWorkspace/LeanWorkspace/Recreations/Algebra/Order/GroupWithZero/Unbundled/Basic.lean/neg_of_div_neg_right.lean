import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [LinearOrder G₀] {a b c d : G₀}

variable [PosMulMono G₀]

theorem neg_of_div_neg_right (h : a / b < 0) (ha : 0 ≤ a) : b < 0 := have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb ↦ (div_nonneg ha hb).not_gt h

