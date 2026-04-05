import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [PartialOrder α] [One α]

theorem coe_one : ((1 : Interval α) : Set α) = 1 := Icc_self _

