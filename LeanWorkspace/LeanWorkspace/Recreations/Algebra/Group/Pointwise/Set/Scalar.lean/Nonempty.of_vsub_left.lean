import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty := .of_image2_left

