import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

variable (s t : NonemptyInterval α) {a b : α}

theorem pure_sub_pure (a b : α) : pure a - pure b = pure (a - b) := rfl

