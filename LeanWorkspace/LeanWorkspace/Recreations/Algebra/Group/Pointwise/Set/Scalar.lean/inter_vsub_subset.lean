import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) := image2_inter_subset_left

