import Mathlib

variable {K L : Type*}

variable [Field K]

theorem div_sub' {a b c : K} (hc : c ≠ 0) : a / c - b = (a - c * b) / c := by
  simpa using div_sub_div a b hc one_ne_zero

-- see Note [lower instance priority]

