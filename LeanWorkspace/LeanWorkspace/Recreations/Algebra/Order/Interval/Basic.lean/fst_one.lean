import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [One α]

theorem fst_one : (1 : NonemptyInterval α).fst = 1 := rfl

