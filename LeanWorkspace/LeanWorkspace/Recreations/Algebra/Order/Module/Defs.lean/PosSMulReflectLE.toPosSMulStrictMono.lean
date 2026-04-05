import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [LinearOrder β]

variable [Zero α]

theorem PosSMulReflectLE.toPosSMulStrictMono [PosSMulReflectLE α β] : PosSMulStrictMono α β where
  smul_lt_smul_of_pos_left _a ha _b₁ _b₂ hb := not_le.1 fun h ↦ hb.not_ge <| le_of_smul_le_smul_left h ha

