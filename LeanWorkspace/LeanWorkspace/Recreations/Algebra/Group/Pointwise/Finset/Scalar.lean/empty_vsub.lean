import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ := image₂_empty_left

