import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Right.mul_le_one [MulRightMono α] {a b : α} (ha : a ≤ 1)
    (hb : b ≤ 1) :
    a * b ≤ 1 := mul_le_of_le_one_of_le ha hb

