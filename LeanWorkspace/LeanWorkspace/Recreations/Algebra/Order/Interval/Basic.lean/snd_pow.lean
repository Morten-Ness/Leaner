import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Monoid α] [Preorder α]

variable [MulLeftMono α] [MulRightMono α]

variable (s : NonemptyInterval α) (a : α) (n : ℕ)

theorem snd_pow : (s ^ n).snd = s.snd ^ n := rfl

