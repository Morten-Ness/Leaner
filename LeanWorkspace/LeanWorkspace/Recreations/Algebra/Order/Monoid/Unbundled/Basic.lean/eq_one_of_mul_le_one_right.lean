import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [PartialOrder α]

variable [MulRightMono α] {a b : α}

theorem eq_one_of_mul_le_one_right (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : b = 1 := hb.eq_of_not_lt' fun h => hab.not_gt <| Right.one_lt_mul_of_le_of_lt ha h

