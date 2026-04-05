import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsRightCancelMul M] {a b : M}

theorem right_ne_mul : b ≠ a * b ↔ a ≠ 1 := right_eq_mul.not

