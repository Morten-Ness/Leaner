import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

variable [@Std.Commutative α (· * ·)]

theorem PosMulMono.toMulPosMono [PosMulMono α] : MulPosMono α := posMulMono_iff_mulPosMono.mp ‹_›

