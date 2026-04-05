import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [Preorder G₀] {a b c : G₀}

theorem inv_mul_right_le (ha : 0 ≤ a) : a * b⁻¹ * b ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

