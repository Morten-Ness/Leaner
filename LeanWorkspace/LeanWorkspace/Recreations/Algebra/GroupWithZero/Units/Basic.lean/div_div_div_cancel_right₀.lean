import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_div_div_cancel_right₀ (hc : c ≠ 0) (a b : G₀) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ hc]

