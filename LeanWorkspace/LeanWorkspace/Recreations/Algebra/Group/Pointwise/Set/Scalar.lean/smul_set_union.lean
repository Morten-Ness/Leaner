import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ := image_union ..

