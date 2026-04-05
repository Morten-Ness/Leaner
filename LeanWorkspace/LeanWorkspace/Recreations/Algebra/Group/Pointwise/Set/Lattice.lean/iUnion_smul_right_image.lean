import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem iUnion_smul_right_image : ⋃ a ∈ t, (· • a) '' s = s • t := iUnion_image_right _

