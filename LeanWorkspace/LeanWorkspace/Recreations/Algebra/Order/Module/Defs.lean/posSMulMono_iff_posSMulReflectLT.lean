import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [LinearOrder β]

variable [Zero α]

theorem posSMulMono_iff_posSMulReflectLT : PosSMulMono α β ↔ PosSMulReflectLT α β := ⟨fun _ ↦ PosSMulMono.toPosSMulReflectLT, fun _ ↦ PosSMulReflectLT.toPosSMulMono⟩

