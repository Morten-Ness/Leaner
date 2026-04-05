import Mathlib

variable {F α β γ : Type*}

variable {s : Set α} {t : Set β} {a : α} {b : β}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem iUnion_vsub_right_image : ⋃ a ∈ t, (· -ᵥ a) '' s = s -ᵥ t := iUnion_image_right _

