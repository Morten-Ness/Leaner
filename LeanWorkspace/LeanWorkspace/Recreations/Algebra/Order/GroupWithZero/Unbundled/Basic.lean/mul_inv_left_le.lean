import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [Preorder G₀] {a b c : G₀}

theorem mul_inv_left_le (hb : 0 ≤ b) : a * (a⁻¹ * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

