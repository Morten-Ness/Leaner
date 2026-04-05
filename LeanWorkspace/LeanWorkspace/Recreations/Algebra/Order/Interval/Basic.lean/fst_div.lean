import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [CommGroup α] [MulLeftMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem fst_div : (s / t).fst = s.fst / t.snd := rfl

