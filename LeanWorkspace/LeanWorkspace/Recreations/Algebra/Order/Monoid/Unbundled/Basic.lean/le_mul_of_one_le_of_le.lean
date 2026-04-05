import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem le_mul_of_one_le_of_le [MulRightMono α] {a b c : α} (ha : 1 ≤ a)
    (hbc : b ≤ c) :
    b ≤ a * c := calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_left ha c

