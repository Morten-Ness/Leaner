import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [PartialOrder α]

variable [MulLeftMono α] {a b : α}

theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 := ha.eq_of_not_lt fun h => hab.not_gt <| mul_lt_one_of_lt_of_le h hb

