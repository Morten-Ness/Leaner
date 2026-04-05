import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := h.isUnit.mul_one_div_cancel

