import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

variable [@Std.Commutative α (· * ·)]

theorem PosMulStrictMono.toMulPosStrictMono [PosMulStrictMono α] : MulPosStrictMono α := posMulStrictMono_iff_mulPosStrictMono.mp ‹_›

