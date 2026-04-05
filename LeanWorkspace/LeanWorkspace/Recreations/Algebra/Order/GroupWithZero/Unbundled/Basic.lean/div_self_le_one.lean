import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [Preorder G₀] [ZeroLEOneClass G₀] {a b c : G₀}

theorem div_self_le_one (a : G₀) : a / a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

