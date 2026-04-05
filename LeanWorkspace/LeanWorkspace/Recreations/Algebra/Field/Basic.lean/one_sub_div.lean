import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b := (same_sub_div h).symm

