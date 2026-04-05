import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem smul_iUnion (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i := image2_iUnion_right ..

