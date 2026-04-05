import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [Preorder α]

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

