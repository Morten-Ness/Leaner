import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_iUnion (a : α) (s : ι → Set β) : a • ⋃ i, s i = ⋃ i, a • s i := image_iUnion

