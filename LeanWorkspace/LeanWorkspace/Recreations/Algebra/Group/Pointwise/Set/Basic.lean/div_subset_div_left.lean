import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ := image2_subset_left

