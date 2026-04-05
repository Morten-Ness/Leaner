import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

