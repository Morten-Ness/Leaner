import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_le_mul_of_nonneg [PosMulMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 ≤ d) : a * c ≤ b * d := (mul_le_mul_of_nonneg_left h₂ a0).trans (mul_le_mul_of_nonneg_right h₁ d0)

