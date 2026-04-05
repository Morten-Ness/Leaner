import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s := image2_singleton_right

