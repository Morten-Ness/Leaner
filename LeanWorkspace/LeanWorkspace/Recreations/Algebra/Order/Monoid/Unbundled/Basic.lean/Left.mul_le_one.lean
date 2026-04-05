import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Left.mul_le_one [MulLeftMono α] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 := mul_le_of_le_of_le_one ha hb

