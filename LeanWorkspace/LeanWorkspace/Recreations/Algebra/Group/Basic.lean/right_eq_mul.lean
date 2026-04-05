import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsRightCancelMul M] {a b : M}

theorem right_eq_mul : b = a * b ↔ a = 1 := eq_comm.trans mul_eq_right

