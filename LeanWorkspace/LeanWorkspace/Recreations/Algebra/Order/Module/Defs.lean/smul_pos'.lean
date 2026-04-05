import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [Preorder β]

theorem smul_pos' [SMulPosStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0 < a • b := by
  simpa only [zero_smul] using smul_lt_smul_of_pos_right ha hb

