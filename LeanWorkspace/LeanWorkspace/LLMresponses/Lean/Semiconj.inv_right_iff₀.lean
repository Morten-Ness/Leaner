import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a x y x' y' : G₀}

theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y := by
  constructor <;> intro h
  · simpa using h.inv_right₀
  · simpa using h.inv_right₀
