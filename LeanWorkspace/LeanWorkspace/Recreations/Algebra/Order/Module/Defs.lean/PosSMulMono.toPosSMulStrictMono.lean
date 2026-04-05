import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Semiring α] [AddCommGroup β] [Module α β]

variable [IsDomain α] [Module.IsTorsionFree α β]

variable [Preorder α] [PartialOrder β]

theorem PosSMulMono.toPosSMulStrictMono [PosSMulMono α β] : PosSMulStrictMono α β := ⟨fun _a ha _b₁ _b₂ hb ↦ (smul_le_smul_of_nonneg_left hb.le ha.le).lt_of_ne <|
    (smul_right_injective _ ha.ne').ne hb.ne⟩

