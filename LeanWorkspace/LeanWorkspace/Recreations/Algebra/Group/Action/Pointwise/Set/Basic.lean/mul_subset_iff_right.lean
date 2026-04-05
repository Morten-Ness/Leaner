import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u := image2_subset_iff_right

