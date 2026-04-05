import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero α] [Zero β]

theorem smul_lt_smul_of_le_of_lt' [PosSMulStrictMono α β] [SMulPosMono α β] (ha : a₁ ≤ a₂)
    (hb : b₁ < b₂) (h₂ : 0 < a₂) (h₁ : 0 ≤ b₁) : a₁ • b₁ < a₂ • b₂ := (smul_le_smul_of_nonneg_right ha h₁).trans_lt (smul_lt_smul_of_pos_left hb h₂)

