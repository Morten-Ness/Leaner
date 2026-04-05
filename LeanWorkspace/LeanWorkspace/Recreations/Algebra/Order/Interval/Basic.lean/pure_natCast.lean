import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [NatCast α]

theorem pure_natCast (n : ℕ) : pure (n : α) = n := rfl

