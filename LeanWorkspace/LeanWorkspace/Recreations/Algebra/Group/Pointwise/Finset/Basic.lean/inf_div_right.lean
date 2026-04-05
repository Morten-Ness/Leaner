import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem inf_div_right [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf t fun y ↦ inf s (f <| · / y) := inf_image₂_right ..

