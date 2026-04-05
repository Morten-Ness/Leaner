import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [Preorder G₀] [ZeroLEOneClass G₀] {a b c : G₀}

theorem inv_mul_le_one : a⁻¹ * a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

