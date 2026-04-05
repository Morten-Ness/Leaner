import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [CommGroup α] [MulLeftMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem pure_div_pure : pure a / pure b = pure (a / b) := rfl

