import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t := image2_subset_right

