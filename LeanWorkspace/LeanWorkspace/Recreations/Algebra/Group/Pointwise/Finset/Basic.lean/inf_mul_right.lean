import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem inf_mul_right {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s * t) f = inf t fun y ↦ inf s (f <| · * y) := inf_image₂_right ..

