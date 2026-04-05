import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem vsub_iInter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    s -ᵥ ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, s -ᵥ t i j := image2_iInter₂_subset_right ..

