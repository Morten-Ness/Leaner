import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulZeroClass α β]

variable [Preorder α] [Preorder β]

theorem neg_of_smul_neg_left [PosSMulReflectLT α β] (h : a • b < 0) (ha : 0 ≤ a) : b < 0 := lt_of_smul_lt_smul_left (by rwa [smul_zero]) ha

