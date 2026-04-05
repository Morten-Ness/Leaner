import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem sUnion_div (S : Set (Set α)) (t : Set α) : ⋃₀ S / t = ⋃ s ∈ S, s / t := image2_sUnion_left ..

