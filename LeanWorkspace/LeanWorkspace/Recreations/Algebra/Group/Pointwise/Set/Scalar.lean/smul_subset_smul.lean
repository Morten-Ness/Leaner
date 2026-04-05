import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image2_subset

