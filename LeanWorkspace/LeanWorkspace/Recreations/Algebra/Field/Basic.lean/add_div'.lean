import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem add_div' (a b c : K) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  rw [add_div, mul_div_cancel_right₀ _ hc]

