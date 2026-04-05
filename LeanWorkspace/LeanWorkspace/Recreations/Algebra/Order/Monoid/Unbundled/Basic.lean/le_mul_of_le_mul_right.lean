import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem le_mul_of_le_mul_right [MulRightMono α] {a b c d : α}
    (h : a ≤ b * c) (hle : b ≤ d) :
    a ≤ d * c := h.trans (mul_le_mul_left hle c)

