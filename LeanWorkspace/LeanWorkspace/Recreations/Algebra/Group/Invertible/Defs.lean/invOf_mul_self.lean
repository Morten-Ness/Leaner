import Mathlib

variable {α : Type u}

theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟a * a = 1 := invOf_mul_self' _

