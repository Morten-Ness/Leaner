import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_mul_cancel_of_imp (h : b = 0 → a = 0) : a / b * b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

