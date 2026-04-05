import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem snd_mul : (s * t).snd = s.snd * t.snd := rfl

