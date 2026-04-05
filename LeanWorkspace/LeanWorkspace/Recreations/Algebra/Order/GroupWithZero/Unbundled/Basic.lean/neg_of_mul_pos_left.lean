import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [LinearOrder α]

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 := ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1

