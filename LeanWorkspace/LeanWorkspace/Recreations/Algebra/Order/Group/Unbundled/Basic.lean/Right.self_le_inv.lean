import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulRightMono α] {a : α}

theorem Right.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ := le_trans h (Right.one_le_inv_iff.mpr h)

