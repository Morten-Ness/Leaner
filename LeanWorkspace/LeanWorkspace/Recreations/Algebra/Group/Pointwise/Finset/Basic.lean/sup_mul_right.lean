import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem sup_mul_right {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s * t) f = sup t fun y ↦ sup s (f <| · * y) := sup_image₂_right ..

