import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem Right.mul_lt_mul [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α}
    (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d := mul_lt_mul_of_lt_of_le h₁ h₂.le

