import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

variable [@Std.Commutative α (· * ·)]

theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp only [posMulReflectLE_iff, mulPosReflectLE_iff, Std.Commutative.comm]

