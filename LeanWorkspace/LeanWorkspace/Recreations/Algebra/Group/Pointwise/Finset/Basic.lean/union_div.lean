import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t := image₂_union_left

