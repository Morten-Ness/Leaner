import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [NatCast α]

theorem snd_natCast (n : ℕ) : (n : NonemptyInterval α).snd = n := rfl

