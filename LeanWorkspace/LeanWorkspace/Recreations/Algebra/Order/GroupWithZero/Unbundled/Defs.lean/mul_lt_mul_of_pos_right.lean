import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_mul_of_pos_right [MulPosStrictMono α] (hbc : b < c) (ha : 0 < a) : b * a < c * a := MulPosStrictMono.mul_lt_mul_of_pos_right ha hbc

