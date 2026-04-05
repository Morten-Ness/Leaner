import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [One α]

theorem pure_one : pure (1 : α) = 1 := rfl

