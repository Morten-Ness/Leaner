import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem toProd_mul : (s * t).toProd = s.toProd * t.toProd := rfl

