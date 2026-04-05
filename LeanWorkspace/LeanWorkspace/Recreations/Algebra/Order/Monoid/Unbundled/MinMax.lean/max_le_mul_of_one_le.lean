import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [MulOneClass α]

theorem max_le_mul_of_one_le [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b := max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

