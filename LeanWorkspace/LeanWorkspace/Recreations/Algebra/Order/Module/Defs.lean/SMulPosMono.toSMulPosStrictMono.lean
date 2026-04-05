import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [AddCommGroup β] [Module α β] [PartialOrder α] [PartialOrder β]

variable [IsDomain α] [Module.IsTorsionFree α β]

theorem SMulPosMono.toSMulPosStrictMono [SMulPosMono α β] : SMulPosStrictMono α β := ⟨fun _b hb _a₁ _a₂ ha ↦ (smul_le_smul_of_nonneg_right ha.le hb.le).lt_of_ne <|
    (smul_left_injective _ hb.ne').ne ha.ne⟩

