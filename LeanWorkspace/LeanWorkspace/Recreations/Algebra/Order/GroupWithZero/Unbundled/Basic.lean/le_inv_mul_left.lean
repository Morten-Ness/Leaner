import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [Preorder G₀] {a b c : G₀}

theorem le_inv_mul_left (hb : b ≤ 0) : b ≤ a⁻¹ * (a * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

