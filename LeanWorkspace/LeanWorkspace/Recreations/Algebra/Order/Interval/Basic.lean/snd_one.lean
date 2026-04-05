import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [One α]

theorem snd_one : (1 : NonemptyInterval α).snd = 1 := rfl

