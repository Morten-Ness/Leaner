import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_iInter_subset (a : α) (t : ι → Set β) : a • ⋂ i, t i ⊆ ⋂ i, a • t i := image_iInter_subset ..

