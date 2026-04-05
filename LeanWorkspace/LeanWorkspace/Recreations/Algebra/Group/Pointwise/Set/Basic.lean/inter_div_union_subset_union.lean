import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem inter_div_union_subset_union : s₁ ∩ s₂ / (t₁ ∪ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ := image2_inter_union_subset_union

