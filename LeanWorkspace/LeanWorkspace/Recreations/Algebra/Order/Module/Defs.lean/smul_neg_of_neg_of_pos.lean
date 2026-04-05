import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [Preorder β]

theorem smul_neg_of_neg_of_pos [SMulPosStrictMono α β] (ha : a < 0) (hb : 0 < b) : a • b < 0 := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

