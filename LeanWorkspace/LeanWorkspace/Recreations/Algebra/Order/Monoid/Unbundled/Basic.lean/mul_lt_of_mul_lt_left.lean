import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_lt_of_mul_lt_left [MulLeftMono α] {a b c d : α} (h : a * b < c)
    (hle : d ≤ b) :
    a * d < c := (mul_le_mul_right hle a).trans_lt h

