import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    b * a < c * a ↔ b < c where
  mp h := lt_of_mul_lt_mul_right h a0.le
  mpr h := mul_lt_mul_of_pos_right h a0

