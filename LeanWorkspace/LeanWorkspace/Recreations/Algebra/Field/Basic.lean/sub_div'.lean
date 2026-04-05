import Mathlib

variable {K L : Type*}

variable [Field K]

theorem sub_div' {a b c : K} (hc : c ≠ 0) : b - a / c = (b * c - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc

