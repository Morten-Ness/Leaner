import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem same_add_div (h : b ≠ 0) : (b + a) / b = 1 + a / b := by rw [← div_self h, add_div]

