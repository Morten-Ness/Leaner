import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [AddCommGroup β] [Module α β] [PartialOrder α] [PartialOrder β]

variable [IsDomain α] [Module.IsTorsionFree α β]

theorem SMulPosReflectLE_iff_smulPosReflectLT : SMulPosReflectLE α β ↔ SMulPosReflectLT α β := ⟨fun _ ↦ inferInstance, fun _ ↦ SMulPosReflectLT.toSMulPosReflectLE⟩

