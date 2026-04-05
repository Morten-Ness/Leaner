import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Monoid α] [Zero β] [MulAction α β]

variable [Preorder α] [Preorder β]

theorem smul_lt_of_lt_one_left [SMulPosStrictMono α β] (hb : 0 < b) (h : a < 1) : a • b < b := by
  simpa only [one_smul] using smul_lt_smul_of_pos_right h hb

