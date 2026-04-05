import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem mk_val (u : αˣ) (y h₁ h₂) : Units.mk (u : α) y h₁ h₂ = u := Units.ext rfl

