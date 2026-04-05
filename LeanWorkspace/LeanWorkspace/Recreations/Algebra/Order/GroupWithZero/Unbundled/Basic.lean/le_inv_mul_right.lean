import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [Preorder G₀] {a b c : G₀}

theorem le_inv_mul_right (ha : a ≤ 0) : a ≤ a * b⁻¹ * b := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

