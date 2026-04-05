import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
    a ≤ b * d := h.trans (mul_le_mul_of_nonneg_left hle b0)

