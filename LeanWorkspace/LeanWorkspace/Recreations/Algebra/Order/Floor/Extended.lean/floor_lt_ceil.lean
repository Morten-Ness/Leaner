import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem floor_lt_ceil (hrs : r < s) : ⌊r⌋ₑ < ⌈s⌉ₑ := floor_lt.2 <| hrs.trans_le le_ceil_self

