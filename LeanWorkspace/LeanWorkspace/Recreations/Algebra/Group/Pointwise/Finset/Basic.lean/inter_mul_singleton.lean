import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem inter_mul_singleton (s t : Finset α) (a : α) : s ∩ t * {a} = s * {a} ∩ (t * {a}) := image₂_inter_singleton _ _ <| mul_left_injective _

