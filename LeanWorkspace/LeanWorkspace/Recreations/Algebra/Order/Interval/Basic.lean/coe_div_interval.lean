import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [CommGroup α] [MulLeftMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem coe_div_interval : (↑(s / t) : Interval α) = s / t := rfl

