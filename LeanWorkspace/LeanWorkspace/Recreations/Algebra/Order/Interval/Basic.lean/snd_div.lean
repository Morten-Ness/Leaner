import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [CommGroup α] [MulLeftMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem snd_div : (s / t).snd = s.snd / t.fst := rfl

