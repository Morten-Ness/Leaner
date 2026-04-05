import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [Preorder β]

theorem pos_of_smul_pos_right [SMulPosReflectLT α β] (h : 0 < a • b) (hb : 0 ≤ b) : 0 < a := lt_of_smul_lt_smul_right (by rwa [zero_smul]) hb

