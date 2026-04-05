import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_iUnion (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i := image2_iUnion_right ..

