import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t := coe_image₂ _ _ _

