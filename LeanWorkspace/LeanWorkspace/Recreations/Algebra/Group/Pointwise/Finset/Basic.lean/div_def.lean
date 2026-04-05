import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem div_def : s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2 := rfl

