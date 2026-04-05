import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty := Nonempty.of_image₂_left

