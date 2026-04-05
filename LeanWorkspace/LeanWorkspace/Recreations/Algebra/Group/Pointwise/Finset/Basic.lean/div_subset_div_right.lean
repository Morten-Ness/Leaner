import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t := image₂_subset_right

