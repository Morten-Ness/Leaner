import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem div_subset_div : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ / t₁ ⊆ s₂ / t₂ := image₂_subset

