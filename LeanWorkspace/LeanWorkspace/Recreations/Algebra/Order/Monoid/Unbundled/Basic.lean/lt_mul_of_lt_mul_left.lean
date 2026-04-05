import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem lt_mul_of_lt_mul_left [MulLeftMono α] {a b c d : α} (h : a < b * c)
    (hle : c ≤ d) :
    a < b * d := h.trans_le (mul_le_mul_right hle b)

