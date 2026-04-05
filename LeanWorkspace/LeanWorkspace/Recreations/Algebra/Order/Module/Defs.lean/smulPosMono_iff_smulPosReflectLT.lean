import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [LinearOrder α] [LinearOrder β]

variable [Zero β]

theorem smulPosMono_iff_smulPosReflectLT : SMulPosMono α β ↔ SMulPosReflectLT α β := ⟨fun _ ↦ SMulPosMono.toSMulPosReflectLT, fun _ ↦ SMulPosReflectLT.toSMulPosMono⟩

