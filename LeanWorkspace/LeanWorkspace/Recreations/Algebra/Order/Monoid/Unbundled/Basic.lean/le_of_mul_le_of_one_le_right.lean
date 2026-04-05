import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem le_of_mul_le_of_one_le_right [MulRightMono α] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) :
    b ≤ c := (le_mul_of_one_le_left' hle).trans h

