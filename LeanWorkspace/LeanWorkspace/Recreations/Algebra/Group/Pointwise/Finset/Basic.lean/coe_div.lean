import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t := coe_image₂ _ _ _

