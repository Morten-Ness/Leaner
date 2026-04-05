import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by simp [div_eq_mul_inv]

