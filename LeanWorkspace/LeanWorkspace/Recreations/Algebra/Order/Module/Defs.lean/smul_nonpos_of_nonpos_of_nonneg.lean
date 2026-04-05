import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [Preorder β]

theorem smul_nonpos_of_nonpos_of_nonneg [SMulPosMono α β] (ha : a ≤ 0) (hb : 0 ≤ b) : a • b ≤ 0 := by
  simpa only [zero_smul] using smul_le_smul_of_nonneg_right ha hb

