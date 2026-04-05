import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a := rfl

