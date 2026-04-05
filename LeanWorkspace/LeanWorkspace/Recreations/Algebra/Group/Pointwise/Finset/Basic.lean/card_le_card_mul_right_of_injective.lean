import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem card_le_card_mul_right_of_injective (hat : a ∈ t) (ha : Function.Injective (· * a)) :
    #s ≤ #(s * t) := card_le_card_image₂_right _ hat ha

