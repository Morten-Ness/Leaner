import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsRightCancelMul M] {a b : M}

theorem mul_ne_right : a * b ≠ b ↔ a ≠ 1 := mul_eq_right.not

