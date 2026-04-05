import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

variable [@Std.Commutative α (· * ·)]

theorem PosMulReflectLT.toMulPosReflectLT [PosMulReflectLT α] : MulPosReflectLT α := posMulReflectLT_iff_mulPosReflectLT.mp ‹_›

