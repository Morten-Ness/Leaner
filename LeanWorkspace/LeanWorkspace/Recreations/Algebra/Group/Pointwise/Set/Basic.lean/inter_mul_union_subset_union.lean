import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ := image2_inter_union_subset_union

