import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

