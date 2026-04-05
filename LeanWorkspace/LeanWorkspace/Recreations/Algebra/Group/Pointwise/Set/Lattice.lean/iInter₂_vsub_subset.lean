import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem iInter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ i, ⋂ j, s i j) -ᵥ t ⊆ ⋂ i, ⋂ j, s i j -ᵥ t := image2_iInter₂_subset_left ..

