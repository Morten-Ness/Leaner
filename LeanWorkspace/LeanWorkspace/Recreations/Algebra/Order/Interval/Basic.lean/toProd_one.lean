import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [One α]

theorem toProd_one : (1 : NonemptyInterval α).toProd = 1 := rfl

