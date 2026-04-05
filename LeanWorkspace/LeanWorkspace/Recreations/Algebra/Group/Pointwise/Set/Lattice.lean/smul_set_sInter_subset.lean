import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_sInter_subset (a : α) (S : Set (Set β)) :
    a • ⋂₀ S ⊆ ⋂ s ∈ S, a • s := image_sInter_subset ..

