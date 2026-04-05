import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem lt_mul_of_lt_mul_right [MulRightMono α] {a b c d : α}
    (h : a < b * c) (hle : b ≤ d) :
    a < d * c := h.trans_le (mul_le_mul_left hle c)

