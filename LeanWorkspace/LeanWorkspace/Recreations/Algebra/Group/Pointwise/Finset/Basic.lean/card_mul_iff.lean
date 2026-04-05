import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem card_mul_iff :
    #(s * t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 := card_image₂_iff

