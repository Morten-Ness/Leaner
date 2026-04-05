import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_le_mul_of_nonneg' [PosMulMono α] [MulPosMono α]
    (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d := (mul_le_mul_of_nonneg_right h₁ c0).trans (mul_le_mul_of_nonneg_left h₂ b0)

