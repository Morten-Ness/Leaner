import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem Left.mul_lt_mul [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d := mul_lt_mul_of_le_of_lt h₁.le h₂

