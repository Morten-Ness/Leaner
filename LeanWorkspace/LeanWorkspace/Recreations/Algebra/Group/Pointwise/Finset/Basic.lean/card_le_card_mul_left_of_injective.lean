import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem card_le_card_mul_left_of_injective (has : a ∈ s) (ha : Function.Injective (a * ·)) :
    #t ≤ #(s * t) := card_le_card_image₂_left _ has ha

