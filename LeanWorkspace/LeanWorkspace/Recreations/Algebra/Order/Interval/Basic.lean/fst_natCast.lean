import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [NatCast α]

theorem fst_natCast (n : ℕ) : (n : NonemptyInterval α).fst = n := rfl

