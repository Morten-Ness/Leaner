import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Zero α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_left₀ [IsLeftCancelMulZero α] (has : a ∈ s) (ha : a ≠ 0) : #t ≤ #(s * t) := card_le_card_mul_left_of_injective has (mul_right_injective₀ ha)

