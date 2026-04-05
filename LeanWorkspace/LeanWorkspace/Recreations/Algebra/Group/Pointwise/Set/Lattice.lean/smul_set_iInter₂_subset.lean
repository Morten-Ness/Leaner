import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_iInter₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    a • ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, a • t i j := image_iInter₂_subset ..

