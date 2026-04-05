import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b := (div_sub_same h).symm

