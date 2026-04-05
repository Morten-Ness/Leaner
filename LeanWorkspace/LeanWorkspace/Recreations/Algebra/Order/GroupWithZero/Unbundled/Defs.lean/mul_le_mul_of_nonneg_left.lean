import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c := PosMulMono.mul_le_mul_of_nonneg_left ha hbc

