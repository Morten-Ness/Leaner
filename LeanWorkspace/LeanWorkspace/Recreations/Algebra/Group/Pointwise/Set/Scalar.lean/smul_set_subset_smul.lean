import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem smul_set_subset_smul {s : Set α} : a ∈ s → a • t ⊆ s • t := image_subset_image2_right

