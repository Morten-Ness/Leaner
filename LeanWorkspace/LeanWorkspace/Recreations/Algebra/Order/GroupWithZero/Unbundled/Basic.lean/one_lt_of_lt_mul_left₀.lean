import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem one_lt_of_lt_mul_left₀ [PosMulReflectLT α] (ha : 0 ≤ a) (h : a < a * b) : 1 < b := lt_of_mul_lt_mul_left (by simpa) ha

