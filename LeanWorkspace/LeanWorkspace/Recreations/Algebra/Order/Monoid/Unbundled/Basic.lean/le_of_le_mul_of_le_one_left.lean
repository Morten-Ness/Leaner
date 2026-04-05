import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem le_of_le_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) :
    a ≤ b := h.trans (mul_le_of_le_one_right' hle)

