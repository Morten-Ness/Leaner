import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem le_inf_div [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α → β} {a : β} :
    a ≤ inf (s / t) f ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ f (x / y) := le_inf_image₂

