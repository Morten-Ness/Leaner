import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α where
  mul_le_mul_of_nonneg_right _a ha _b _c hbc := not_lt.1 fun h ↦ hbc.not_gt <| lt_of_mul_lt_mul_right h ha

