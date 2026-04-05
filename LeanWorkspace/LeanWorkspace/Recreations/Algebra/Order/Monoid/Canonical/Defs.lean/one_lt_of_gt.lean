import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [Preorder α] [CanonicallyOrderedMul α] {a b : α}

theorem one_lt_of_gt (h : a < b) : 1 < b := (one_le _).trans_lt h

alias LT.lt.pos := pos_of_gt

