import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [MulOneClass α]

theorem min_le_mul_of_one_le_left [MulRightMono α] {a b : α} (ha : 1 ≤ a) :
    min a b ≤ a * b := min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha

