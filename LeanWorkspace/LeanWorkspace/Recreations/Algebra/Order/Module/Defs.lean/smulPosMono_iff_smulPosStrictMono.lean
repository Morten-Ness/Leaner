import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [AddCommGroup β] [Module α β] [PartialOrder α] [PartialOrder β]

variable [IsDomain α] [Module.IsTorsionFree α β]

theorem smulPosMono_iff_smulPosStrictMono : SMulPosMono α β ↔ SMulPosStrictMono α β := ⟨fun _ ↦ SMulPosMono.toSMulPosStrictMono, fun _ ↦ inferInstance⟩

