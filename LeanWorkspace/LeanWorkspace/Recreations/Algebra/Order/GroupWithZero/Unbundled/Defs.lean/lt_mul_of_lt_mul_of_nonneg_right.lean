import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
    a < d * c := h.trans_le (mul_le_mul_of_nonneg_right hle c0)

