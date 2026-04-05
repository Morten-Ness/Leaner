import Mathlib

variable {α β γ : Type*}

theorem map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : WithOne.map₂ f a b = f a b := rfl

