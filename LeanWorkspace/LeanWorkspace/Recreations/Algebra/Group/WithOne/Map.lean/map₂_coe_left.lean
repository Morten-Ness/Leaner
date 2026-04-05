import Mathlib

variable {α β γ : Type*}

theorem map₂_coe_left (f : α → β → γ) (a : α) (b) : WithOne.map₂ f a b = b.map fun b ↦ f a b := rfl

