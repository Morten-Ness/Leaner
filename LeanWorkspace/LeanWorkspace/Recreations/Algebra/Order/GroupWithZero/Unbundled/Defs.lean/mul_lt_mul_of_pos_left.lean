import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc : b < c) (ha : 0 < a) : a * b < a * c := PosMulStrictMono.mul_lt_mul_of_pos_left ha hbc

