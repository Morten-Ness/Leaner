import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem div_add_same (h : b ≠ 0) : (a + b) / b = a / b + 1 := by rw [← div_self h, add_div]

