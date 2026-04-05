import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_le_mul_three [MulLeftMono α]
    [MulRightMono α] {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e)
    (h₃ : c ≤ f) :
    a * b * c ≤ d * e * f := mul_le_mul' (mul_le_mul' h₁ h₂) h₃

