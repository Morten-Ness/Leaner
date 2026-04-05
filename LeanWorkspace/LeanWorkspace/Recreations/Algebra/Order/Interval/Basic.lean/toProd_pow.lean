import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Monoid α] [Preorder α]

variable [MulLeftMono α] [MulRightMono α]

variable (s : NonemptyInterval α) (a : α) (n : ℕ)

theorem toProd_pow : (s ^ n).toProd = s.toProd ^ n := rfl

