import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_lt_mul_of_le_of_lt [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) :
    a * c < b * d := (mul_le_mul_left h₁ _).trans_lt (mul_lt_mul_right h₂ b)

