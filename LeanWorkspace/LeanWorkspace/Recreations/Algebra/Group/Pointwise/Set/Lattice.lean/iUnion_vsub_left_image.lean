import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem iUnion_vsub_left_image : ⋃ a ∈ s, (a -ᵥ ·) '' t = s -ᵥ t := iUnion_image_left _

