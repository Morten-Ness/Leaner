import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero α] [Zero β]

theorem smul_lt_smul_of_lt_of_le' [PosSMulMono α β] [SMulPosStrictMono α β] (ha : a₁ < a₂)
    (hb : b₁ ≤ b₂) (h₂ : 0 ≤ a₂) (h₁ : 0 < b₁) : a₁ • b₁ < a₂ • b₂ := (smul_lt_smul_of_pos_right ha h₁).trans_le (smul_le_smul_of_nonneg_left hb h₂)

