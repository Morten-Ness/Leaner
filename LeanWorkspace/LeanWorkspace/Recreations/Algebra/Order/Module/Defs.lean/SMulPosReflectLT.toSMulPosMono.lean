import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [LinearOrder β]

variable [Zero β]

theorem SMulPosReflectLT.toSMulPosMono [SMulPosReflectLT α β] : SMulPosMono α β where
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := not_lt.1 fun h ↦ ha.not_gt <| lt_of_smul_lt_smul_right h hb

