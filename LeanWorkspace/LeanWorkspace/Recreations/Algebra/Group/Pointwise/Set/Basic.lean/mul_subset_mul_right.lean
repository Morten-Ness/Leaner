import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t := image2_subset_right

