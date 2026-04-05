import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem vsub_iUnion (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i := image2_iUnion_right ..

