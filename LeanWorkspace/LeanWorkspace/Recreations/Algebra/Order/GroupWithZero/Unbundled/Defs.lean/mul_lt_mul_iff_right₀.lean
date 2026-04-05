import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a * c ↔ b < c where
  mp h := lt_of_mul_lt_mul_left h a0.le
  mpr h := mul_lt_mul_of_pos_left h a0

