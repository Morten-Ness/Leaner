import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem pure_mul_pure : pure a * pure b = pure (a * b) := rfl

