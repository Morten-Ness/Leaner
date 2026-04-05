import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulRightStrictMono α] {a : α}

theorem Right.self_lt_inv (h : a < 1) : a < a⁻¹ := lt_trans h (Right.one_lt_inv_iff.mpr h)

