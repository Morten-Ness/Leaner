import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem sup_div_right [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s / t) f = sup t fun y ↦ sup s (f <| · / y) := sup_image₂_right ..

