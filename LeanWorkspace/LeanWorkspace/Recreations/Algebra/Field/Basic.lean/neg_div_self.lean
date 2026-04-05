import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem neg_div_self {a : K} (h : a ≠ 0) : -a / a = -1 := by rw [neg_div, div_self h]

