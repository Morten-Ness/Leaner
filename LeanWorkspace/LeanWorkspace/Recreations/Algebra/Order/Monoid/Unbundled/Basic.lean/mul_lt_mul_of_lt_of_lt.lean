import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α]
    [MulRightStrictMono α]
    {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d := calc
    a * c < a * d := mul_lt_mul_right h₂ a
    _ < b * d := mul_lt_mul_left h₁ d

alias add_lt_add := add_lt_add_of_lt_of_lt

