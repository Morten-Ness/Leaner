import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_iUnion₂ (a : α) (s : ∀ i, κ i → Set β) :
    a • ⋃ i, ⋃ j, s i j = ⋃ i, ⋃ j, a • s i j := image_iUnion₂ ..

