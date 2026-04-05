import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t := mem_image₂_of_mem

