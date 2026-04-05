import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [LinearOrder β]

variable [Zero β]

theorem SMulPosReflectLE.toSMulPosStrictMono [SMulPosReflectLE α β] : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := not_le.1 fun h ↦ ha.not_ge <| le_of_smul_le_smul_of_pos_right h hb

