import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} := image₂_singleton

