import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α := ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩

