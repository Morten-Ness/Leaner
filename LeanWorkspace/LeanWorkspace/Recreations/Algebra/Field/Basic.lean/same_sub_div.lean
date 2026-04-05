import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

