import Mathlib

variable {α β γ : Type*}

theorem map₂_bot_left (f : α → β → γ) (b) : WithOne.map₂ f 1 b = 1 := rfl

