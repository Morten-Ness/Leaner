import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b ∈ s, ∃ c ∈ t, b -ᵥ c = a := mem_image₂

