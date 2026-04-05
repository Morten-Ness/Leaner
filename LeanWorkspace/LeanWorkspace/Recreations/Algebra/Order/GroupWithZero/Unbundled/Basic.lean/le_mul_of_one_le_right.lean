import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

