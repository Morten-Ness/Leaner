import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem smul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ i, ⋂ j, t i j) ⊆ ⋂ i, ⋂ j, s • t i j := image2_iInter₂_subset_right ..

