import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulLeftStrictMono α] {a : α}

theorem Left.inv_lt_self (h : 1 < a) : a⁻¹ < a := (Left.inv_lt_one_iff.mpr h).trans h

alias neg_lt_self := Left.neg_lt_self

