import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_singleton_mul (a : α) (t : Finset α) : #({a} * t) = #t := card_image₂_singleton_left _ <| mul_right_injective _

