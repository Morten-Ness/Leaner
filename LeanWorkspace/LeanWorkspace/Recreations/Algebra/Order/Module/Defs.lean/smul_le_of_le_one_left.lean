import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Monoid α] [Zero β] [MulAction α β]

variable [Preorder α] [Preorder β]

theorem smul_le_of_le_one_left [SMulPosMono α β] (hb : 0 ≤ b) (h : a ≤ 1) : a • b ≤ b := by
  simpa only [one_smul] using smul_le_smul_of_nonneg_right h hb

