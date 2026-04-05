import Mathlib

variable {α β γ : Type*}

theorem map₂_bot_right (f : α → β → γ) (a) : WithOne.map₂ f a 1 = 1 := by cases a <;> rfl

