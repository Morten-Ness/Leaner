import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

theorem iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a ∈ s, a • t = s • t := iUnion_image_left _

