import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem mem_div : a ∈ s / t ↔ ∃ b ∈ s, ∃ c ∈ t, b / c = a := mem_image₂

