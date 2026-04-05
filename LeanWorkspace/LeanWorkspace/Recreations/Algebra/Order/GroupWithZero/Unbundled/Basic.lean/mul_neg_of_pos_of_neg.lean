import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

