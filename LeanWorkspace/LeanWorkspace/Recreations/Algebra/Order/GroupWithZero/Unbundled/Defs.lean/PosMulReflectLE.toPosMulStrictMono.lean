import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc := not_le.1 fun h ↦ hbc.not_ge <| le_of_mul_le_mul_left h ha

