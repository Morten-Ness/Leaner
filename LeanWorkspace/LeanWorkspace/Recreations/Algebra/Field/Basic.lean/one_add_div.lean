import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem one_add_div (h : b ≠ 0) : 1 + a / b = (b + a) / b := (same_add_div h).symm

