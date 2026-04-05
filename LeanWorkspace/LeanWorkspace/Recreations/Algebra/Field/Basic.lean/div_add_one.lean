import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem div_add_one (h : b ≠ 0) : a / b + 1 = (a + b) / b := (div_add_same h).symm

