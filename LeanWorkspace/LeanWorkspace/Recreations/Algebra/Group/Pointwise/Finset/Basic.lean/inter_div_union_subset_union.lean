import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem inter_div_union_subset_union : s₁ ∩ s₂ / (t₁ ∪ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ := image₂_inter_union_subset_union

