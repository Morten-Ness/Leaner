import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [AddCommGroup β] [Module α β] [PartialOrder α] [PartialOrder β]

variable [IsDomain α] [Module.IsTorsionFree α β]

theorem SMulPosReflectLT.toSMulPosReflectLE [SMulPosReflectLT α β] : SMulPosReflectLE α β := ⟨fun _b hb _a₁ _a₂ h ↦ h.eq_or_lt.elim (fun h ↦ (smul_left_injective _ hb.ne' h).le) fun h' ↦
    (lt_of_smul_lt_smul_right h' hb.le).le⟩

