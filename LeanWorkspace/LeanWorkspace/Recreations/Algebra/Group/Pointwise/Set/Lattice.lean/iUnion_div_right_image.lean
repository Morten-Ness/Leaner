import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem iUnion_div_right_image : ⋃ a ∈ t, (· / a) '' s = s / t := iUnion_image_right _

