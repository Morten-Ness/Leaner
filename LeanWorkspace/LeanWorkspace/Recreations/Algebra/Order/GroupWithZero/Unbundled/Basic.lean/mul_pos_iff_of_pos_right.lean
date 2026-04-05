import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_iff_left₀ (b := 0) h

