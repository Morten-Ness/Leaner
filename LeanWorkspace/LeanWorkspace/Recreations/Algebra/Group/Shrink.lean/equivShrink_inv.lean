import Mathlib

variable {M α : Type*} [Small.{v} α]

theorem equivShrink_inv [Inv α] (x : α) : equivShrink α x⁻¹ = (equivShrink α x)⁻¹ := by
  simp [Equiv.inv_def]

