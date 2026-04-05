import Mathlib

variable {α : Type u}

variable [Group α]

variable [Preorder α]

variable [MulLeftStrictMono α] {a : α}

theorem Left.self_lt_inv (h : a < 1) : a < a⁻¹ := lt_trans h (Left.one_lt_inv_iff.mpr h)

