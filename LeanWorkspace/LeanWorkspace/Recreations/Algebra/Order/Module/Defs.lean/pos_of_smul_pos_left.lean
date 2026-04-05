import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulZeroClass α β]

variable [Preorder α] [Preorder β]

theorem pos_of_smul_pos_left [PosSMulReflectLT α β] (h : 0 < a • b) (ha : 0 ≤ a) : 0 < b := lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

