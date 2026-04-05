import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_lt_mul_of_lt_of_le [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) :
    a * c < b * d := (mul_le_mul_right h₂ _).trans_lt (mul_lt_mul_left h₁ d)

