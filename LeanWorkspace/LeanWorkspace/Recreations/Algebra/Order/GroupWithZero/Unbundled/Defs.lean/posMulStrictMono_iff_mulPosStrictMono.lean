import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

variable [@Std.Commutative α (· * ·)]

theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [posMulStrictMono_iff, mulPosStrictMono_iff, Std.Commutative.comm]

