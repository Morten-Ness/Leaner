import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_le_mul' [MulLeftMono α] [MulRightMono α]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d := by grw [h₁, h₂]

