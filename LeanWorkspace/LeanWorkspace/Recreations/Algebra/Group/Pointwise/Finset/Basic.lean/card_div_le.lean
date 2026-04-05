import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem card_div_le : #(s / t) ≤ #s * #t := card_image₂_le _ _ _

