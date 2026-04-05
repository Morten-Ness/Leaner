import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero α]

theorem monotone_smul_left_of_nonneg [PosSMulMono α β] (ha : 0 ≤ a) : Monotone ((a • ·) : β → β) := PosSMulMono.smul_le_smul_of_nonneg_left ha

