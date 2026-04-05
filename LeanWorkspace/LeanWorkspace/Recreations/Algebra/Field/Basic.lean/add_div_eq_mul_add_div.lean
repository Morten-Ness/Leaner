import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem add_div_eq_mul_add_div (a b : K) (hc : c ≠ 0) : a + b / c = (a * c + b) / c := (eq_div_iff_mul_eq hc).2 <| by rw [right_distrib, div_mul_cancel₀ _ hc]

