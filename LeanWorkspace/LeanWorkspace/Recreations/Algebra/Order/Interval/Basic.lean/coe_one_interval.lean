import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [One α]

theorem coe_one_interval : ((1 : NonemptyInterval α) : Interval α) = 1 := rfl

