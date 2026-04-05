import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [PartialOrder α]

variable [MulLeftMono α] {a b : α}

theorem eq_one_of_mul_le_one_left (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : a = 1 := ha.eq_of_not_lt' fun h => hab.not_gt <| one_lt_mul_of_lt_of_le' h hb

