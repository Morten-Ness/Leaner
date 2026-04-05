import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem lt_of_mul_lt_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) :
    a < c := (le_mul_of_one_le_right' hle).trans_lt h

