import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem inv_mk (x y : α) (h₁ h₂) : (Units.mk x y h₁ h₂)⁻¹ = Units.mk y x h₂ h₁ := rfl

