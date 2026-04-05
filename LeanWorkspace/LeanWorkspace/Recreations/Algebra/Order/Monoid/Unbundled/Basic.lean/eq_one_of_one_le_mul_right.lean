import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [PartialOrder α]

variable [MulRightMono α] {a b : α}

theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 := hb.eq_of_not_lt fun h => hab.not_gt <| Right.mul_lt_one_of_le_of_lt ha h

