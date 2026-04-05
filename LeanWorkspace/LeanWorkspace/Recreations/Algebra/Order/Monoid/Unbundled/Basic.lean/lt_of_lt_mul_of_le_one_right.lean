import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem lt_of_lt_mul_of_le_one_right [MulRightMono α] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) :
    a < c := h.trans_le (mul_le_of_le_one_left' hle)

