import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)

