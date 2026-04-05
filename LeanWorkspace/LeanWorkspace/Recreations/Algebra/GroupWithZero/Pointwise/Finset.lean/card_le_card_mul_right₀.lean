import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_right₀ [IsRightCancelMulZero α] (hat : a ∈ t) (ha : a ≠ 0) : #s ≤ #(s * t) := card_le_card_mul_right_of_injective hat (mul_left_injective₀ ha)

