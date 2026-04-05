import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_self' : #s ≤ #(s * s) := by
  cases s.eq_empty_or_nonempty <;> simp [Finset.card_le_card_mul_right, *]

