import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem Commute.div_sub_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b - c / d = (a * d - b * c) / (b * d) := by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd

