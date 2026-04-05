import Mathlib

variable {α β γ : Type*}

theorem map₂_eq_bot_iff {f : α → β → γ} {a : WithOne α} {b : WithOne β} :
    WithOne.map₂ f a b = 1 ↔ a = 1 ∨ b = 1 := Option.map₂_eq_none_iff

