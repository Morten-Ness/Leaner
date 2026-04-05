import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t := image2_union_left

