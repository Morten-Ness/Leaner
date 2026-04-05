import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} := image₂_singleton

