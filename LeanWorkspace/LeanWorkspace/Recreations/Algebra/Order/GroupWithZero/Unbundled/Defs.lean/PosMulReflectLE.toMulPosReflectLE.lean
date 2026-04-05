import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

variable [@Std.Commutative α (· * ·)]

theorem PosMulReflectLE.toMulPosReflectLE [PosMulReflectLE α] : MulPosReflectLE α := posMulReflectLE_iff_mulPosReflectLE.mp ‹_›

