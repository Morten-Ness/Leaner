import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_iff_right₀ (b := 0) h

