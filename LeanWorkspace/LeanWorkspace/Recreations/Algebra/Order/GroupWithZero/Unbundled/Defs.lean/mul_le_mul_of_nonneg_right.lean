import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : b * a ≤ c * a := MulPosMono.mul_le_mul_of_nonneg_right ha hbc

