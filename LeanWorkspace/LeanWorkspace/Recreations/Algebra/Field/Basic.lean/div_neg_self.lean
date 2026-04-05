import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by rw [div_neg_eq_neg_div, div_self h]

