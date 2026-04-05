import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_self {s : Finset α} : #s ≤ #(s * s) := by
  cases s.eq_empty_or_nonempty <;> simp [Finset.card_le_card_mul_left, *]

