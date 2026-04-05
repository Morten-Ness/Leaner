import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_iInter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i := image2_iInter_subset_right ..

