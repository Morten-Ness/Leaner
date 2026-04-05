import Mathlib

variable {α : Type u}

theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟a = 1 := mul_invOf_self' _

