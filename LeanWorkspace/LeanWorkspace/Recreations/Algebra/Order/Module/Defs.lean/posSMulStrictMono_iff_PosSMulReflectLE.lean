import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [LinearOrder β]

variable [Zero α]

theorem posSMulStrictMono_iff_PosSMulReflectLE : PosSMulStrictMono α β ↔ PosSMulReflectLE α β := ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulReflectLE.toPosSMulStrictMono⟩

