import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectLE α := ⟨@MulPosStrictMono.toMulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩

