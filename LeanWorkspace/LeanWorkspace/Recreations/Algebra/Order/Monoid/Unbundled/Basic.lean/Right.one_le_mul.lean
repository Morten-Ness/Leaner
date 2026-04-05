import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    1 ≤ a * b := le_mul_of_one_le_of_le ha hb

