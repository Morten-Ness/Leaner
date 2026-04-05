import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

variable (s t : NonemptyInterval α) {a b : α}

theorem coe_sub_interval : (↑(s - t) : Interval α) = s - t := rfl

