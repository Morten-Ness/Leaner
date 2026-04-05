import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hle : d ≤ a) (b0 : 0 ≤ b) :
    d * b < c := (mul_le_mul_of_nonneg_right hle b0).trans_lt h

