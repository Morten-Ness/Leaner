import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [LinearOrder α] [Preorder β]

variable [Zero β]

theorem SMulPosMono.toSMulPosReflectLT [SMulPosMono α β] : SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right _b hb _a₁ _a₂ h := not_le.1 fun ha ↦ h.not_ge <| smul_le_smul_of_nonneg_right ha hb

