import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem add_div (a b c : K) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]

