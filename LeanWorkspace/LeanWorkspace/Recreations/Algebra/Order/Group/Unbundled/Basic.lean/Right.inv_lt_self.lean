import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulRightStrictMono α] {a : α}

theorem Right.inv_lt_self (h : 1 < a) : a⁻¹ < a := (Right.inv_lt_one_iff.mpr h).trans h

