import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem inf_div_left [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf s fun x ↦ inf t (f <| x / ·) := inf_image₂_left ..

