import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

variable (s t : NonemptyInterval α) {a b : α}

theorem fst_sub : (s - t).fst = s.fst - t.snd := rfl

