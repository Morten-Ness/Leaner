import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulRightMono α] {a : α}

theorem Right.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a := le_trans (Right.inv_le_one_iff.mpr h) h

