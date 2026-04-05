import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [LinearOrder α]

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 := lt_of_not_ge fun a0 : a ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

