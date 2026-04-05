import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, ← add_div, sub_eq_add_neg]

