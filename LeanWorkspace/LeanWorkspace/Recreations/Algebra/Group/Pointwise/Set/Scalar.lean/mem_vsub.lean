import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ x ∈ s, ∃ y ∈ t, x -ᵥ y = a := Iff.rfl

