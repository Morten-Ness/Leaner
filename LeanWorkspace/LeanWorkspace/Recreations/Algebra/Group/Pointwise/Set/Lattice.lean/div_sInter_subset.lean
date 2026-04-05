import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_sInter_subset (s : Set α) (T : Set (Set α)) : s / ⋂₀ T ⊆ ⋂ t ∈ T, s / t := image2_sInter_subset_right ..

