import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image2_inter_subset_left

