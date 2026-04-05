import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_mul_singleton (s : Finset α) (a : α) : #(s * {a}) = #s := card_image₂_singleton_right _ <| mul_left_injective _

