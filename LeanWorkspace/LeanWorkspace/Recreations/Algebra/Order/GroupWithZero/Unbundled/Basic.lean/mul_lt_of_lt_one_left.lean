import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

