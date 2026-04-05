import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LinearOrder α]

theorem exists_square_le [MulLeftStrictMono α] (a : α) : ∃ b : α, b * b ≤ a := by
  by_cases! h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_right h a
    rw [mul_one] at this
    exact le_of_lt this
  · use 1
    rwa [mul_one]

