import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero β]

theorem monotone_smul_right_of_nonneg [SMulPosMono α β] (hb : 0 ≤ b) : Monotone ((· • b) : α → β) := SMulPosMono.smul_le_smul_of_nonneg_right hb

