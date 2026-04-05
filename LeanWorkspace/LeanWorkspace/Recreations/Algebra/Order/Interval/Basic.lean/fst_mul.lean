import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem fst_mul : (s * t).fst = s.fst * t.fst := rfl

