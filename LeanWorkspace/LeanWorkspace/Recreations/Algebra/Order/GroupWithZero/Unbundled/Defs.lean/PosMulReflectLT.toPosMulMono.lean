import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α where
  mul_le_mul_of_nonneg_left _a ha _b _c hbc := not_lt.1 fun h ↦ hbc.not_gt <| lt_of_mul_lt_mul_left h ha

