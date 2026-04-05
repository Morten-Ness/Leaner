import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

theorem left_eq_mul : a = a * b ↔ b = 1 := eq_comm.trans mul_eq_left

