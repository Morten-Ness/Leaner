import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

variable [@Std.Commutative α (· * ·)]

theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp only [posMulMono_iff, mulPosMono_iff, Std.Commutative.comm]

