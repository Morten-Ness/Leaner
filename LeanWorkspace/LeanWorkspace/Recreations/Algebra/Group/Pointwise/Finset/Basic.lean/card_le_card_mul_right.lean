import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem card_le_card_mul_right (ht : t.Nonempty) : #s ≤ #(s * t) := have ⟨_, ha⟩ := ht; Finset.card_le_card_mul_right_of_injective ha (mul_left_injective _)

