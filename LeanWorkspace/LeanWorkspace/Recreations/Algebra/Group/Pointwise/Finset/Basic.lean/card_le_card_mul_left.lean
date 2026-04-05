import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : #t ≤ #(s * t) := have ⟨_, ha⟩ := hs; Finset.card_le_card_mul_left_of_injective ha (mul_right_injective _)

