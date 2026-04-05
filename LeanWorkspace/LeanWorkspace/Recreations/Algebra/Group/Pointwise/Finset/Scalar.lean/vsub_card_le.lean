import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem vsub_card_le : #(s -ᵥ t : Finset α) ≤ #s * #t := card_image₂_le _ _ _

