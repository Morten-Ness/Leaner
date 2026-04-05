import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulLeftMono α] {a : α}

theorem Left.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a := le_trans (Left.inv_le_one_iff.mpr h) h

alias neg_le_self := Left.neg_le_self

