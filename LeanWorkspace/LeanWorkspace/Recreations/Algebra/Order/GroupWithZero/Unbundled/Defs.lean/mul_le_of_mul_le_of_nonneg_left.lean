import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 ≤ a) :
    a * d ≤ c := (mul_le_mul_of_nonneg_left hle a0).trans h

