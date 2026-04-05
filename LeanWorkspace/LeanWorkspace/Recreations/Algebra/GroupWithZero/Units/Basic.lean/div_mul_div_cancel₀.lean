import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_mul_div_cancel₀ (hb : b ≠ 0) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel₀ _ hb]

