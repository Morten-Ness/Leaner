import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulLeftMono α] {a : α}

theorem Left.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ := le_trans h (Left.one_le_inv_iff.mpr h)

