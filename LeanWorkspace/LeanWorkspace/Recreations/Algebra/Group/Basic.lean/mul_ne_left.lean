import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

theorem mul_ne_left : a * b ≠ a ↔ b ≠ 1 := mul_eq_left.not

