import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [Preorder β]

theorem neg_of_smul_neg_right [SMulPosReflectLT α β] (h : a • b < 0) (hb : 0 ≤ b) : a < 0 := lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

