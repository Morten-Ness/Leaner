import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [LinearOrder β]

variable [Zero α]

theorem PosSMulReflectLT.toPosSMulMono [PosSMulReflectLT α β] : PosSMulMono α β where
  smul_le_smul_of_nonneg_left _a ha _b₁ _b₂ hb := not_lt.1 fun h ↦ hb.not_gt <| lt_of_smul_lt_smul_left h ha

