import Mathlib

variable {α β γ : Type*}

theorem map₂_coe_right (f : α → β → γ) (a) (b : β) : WithOne.map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

