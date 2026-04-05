import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

