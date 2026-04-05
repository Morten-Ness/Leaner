import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem iUnion_div_left_image : ⋃ a ∈ s, (a / ·) '' t = s / t := iUnion_image_left _

