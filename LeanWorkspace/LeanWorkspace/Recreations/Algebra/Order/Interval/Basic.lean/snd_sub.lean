import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

variable (s t : NonemptyInterval α) {a b : α}

theorem snd_sub : (s - t).snd = s.snd - t.fst := rfl

