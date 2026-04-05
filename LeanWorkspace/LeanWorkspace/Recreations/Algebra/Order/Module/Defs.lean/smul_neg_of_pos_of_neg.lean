import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulZeroClass α β]

variable [Preorder α] [Preorder β]

theorem smul_neg_of_pos_of_neg [PosSMulStrictMono α β] (ha : 0 < a) (hb : b < 0) : a • b < 0 := by
  simpa only [smul_zero] using smul_lt_smul_of_pos_left hb ha

