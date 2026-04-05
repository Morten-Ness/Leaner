import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [MulOneClass α]

theorem min_le_mul_of_one_le_right [MulLeftMono α] {a b : α} (hb : 1 ≤ b) :
    min a b ≤ a * b := min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb

