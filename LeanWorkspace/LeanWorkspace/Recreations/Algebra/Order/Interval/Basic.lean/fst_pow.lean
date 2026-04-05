import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Monoid α] [Preorder α]

variable [MulLeftMono α] [MulRightMono α]

variable (s : NonemptyInterval α) (a : α) (n : ℕ)

theorem fst_pow : (s ^ n).fst = s.fst ^ n := rfl

