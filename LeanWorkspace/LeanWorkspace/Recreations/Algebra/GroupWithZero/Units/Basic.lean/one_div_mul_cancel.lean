import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 := h.isUnit.one_div_mul_cancel

