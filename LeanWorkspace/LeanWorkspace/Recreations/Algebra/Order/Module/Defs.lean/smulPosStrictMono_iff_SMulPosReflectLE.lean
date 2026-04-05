import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [LinearOrder α] [LinearOrder β]

variable [Zero β]

theorem smulPosStrictMono_iff_SMulPosReflectLE : SMulPosStrictMono α β ↔ SMulPosReflectLE α β := ⟨fun _ ↦ SMulPosStrictMono.toSMulPosReflectLE, fun _ ↦ SMulPosReflectLE.toSMulPosStrictMono⟩

