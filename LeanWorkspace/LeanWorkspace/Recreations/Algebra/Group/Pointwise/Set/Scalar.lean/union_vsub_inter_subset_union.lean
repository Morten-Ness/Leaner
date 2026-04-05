import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem union_vsub_inter_subset_union : s₁ ∪ s₂ -ᵥ t₁ ∩ t₂ ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) := image2_union_inter_subset_union

