import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) := image₂_singleton_right

