import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc := not_le.1 fun h ↦ hbc.not_ge <| le_of_mul_le_mul_right h ha

