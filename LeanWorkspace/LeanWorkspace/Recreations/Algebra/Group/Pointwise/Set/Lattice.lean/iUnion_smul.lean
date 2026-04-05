import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem iUnion_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t := image2_iUnion_left ..

