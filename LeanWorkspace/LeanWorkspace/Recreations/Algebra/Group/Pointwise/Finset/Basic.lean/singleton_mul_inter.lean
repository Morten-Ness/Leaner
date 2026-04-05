import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem singleton_mul_inter (a : α) (s t : Finset α) : {a} * (s ∩ t) = {a} * s ∩ ({a} * t) := image₂_singleton_inter _ _ <| mul_right_injective _

