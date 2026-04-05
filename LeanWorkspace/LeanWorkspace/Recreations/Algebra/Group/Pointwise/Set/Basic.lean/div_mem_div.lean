import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t := mem_image2_of_mem

