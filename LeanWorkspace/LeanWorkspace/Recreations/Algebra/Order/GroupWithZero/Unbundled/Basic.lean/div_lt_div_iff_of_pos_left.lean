import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

theorem div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b := lt_iff_lt_of_le_iff_le' (div_le_div_iff_of_pos_left ha hc hb)
    (div_le_div_iff_of_pos_left ha hb hc)

-- Not a `mono` lemma b/c `div_le_div₀` is strictly more general

