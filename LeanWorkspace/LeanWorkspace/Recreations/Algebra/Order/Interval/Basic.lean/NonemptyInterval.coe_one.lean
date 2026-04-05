import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [PartialOrder α] [One α]

theorem coe_one : ((1 : NonemptyInterval α) : Set α) = 1 := coe_pure _

