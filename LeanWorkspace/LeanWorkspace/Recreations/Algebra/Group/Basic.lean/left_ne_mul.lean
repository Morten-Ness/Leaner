import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

theorem left_ne_mul : a ≠ a * b ↔ b ≠ 1 := left_eq_mul.not

