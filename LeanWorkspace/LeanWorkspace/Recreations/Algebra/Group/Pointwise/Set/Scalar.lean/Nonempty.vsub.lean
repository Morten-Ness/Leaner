import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Set α).Nonempty := .image2

